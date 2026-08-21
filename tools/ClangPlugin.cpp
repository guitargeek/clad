//--------------------------------------------------------------------*- C++ -*-
// clad - the C++ Clang-based Automatic Differentiator
// version: $Id$
// author:  Vassil Vassilev <vvasilev-at-cern.ch>
//------------------------------------------------------------------------------

#include "ClangPlugin.h"

#include "clad/Differentiator/DerivativeBuilder.h"
#include "clad/Differentiator/DiffPlanner.h"
#include "clad/Differentiator/Sins.h"
#include "clad/Differentiator/Timers.h"
#include "clad/Differentiator/Version.h"
#include "../lib/Differentiator/TBRAnalyzer.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/CodeGenOptions.h"
#include "clang/Basic/LLVM.h" // isa, dyn_cast
#include "clang/Basic/SourceLocation.h"

#ifdef _WIN32
// <windows.h> defines function-like min/max macros that mangle
// std::numeric_limits<>::max() in llvm/ADT/Sequence.h (included below);
// NOMINMAX suppresses them. WIN32_LEAN_AND_MEAN trims unrelated Win32 surface.
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#endif

#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Frontend/MultiplexConsumer.h"
#include "clang/Lex/LexDiagnostic.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"

#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"

#include "clad/Differentiator/CladUtils.h"
#include "clad/Differentiator/Compatibility.h"
#include "clad/Differentiator/DiffMode.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>  // for getenv
#include <iostream> // for std::cerr
#include <memory>
#include <set>

using namespace clang;

namespace clad {
void InitTimers();

  namespace plugin {
    /// Keeps track if we encountered #pragma clad on/off.
    // FIXME: Figure out how to make it a member of CladPlugin.
    std::vector<clang::SourceRange> CladEnabledRange;
    std::set<clang::SourceLocation> CladLoopCheckpoints;

    // Define a pragma handler for #pragma clad
    class CladPragmaHandler : public PragmaHandler {
    public:
      CladPragmaHandler() : PragmaHandler("clad") {}
      void HandlePragma(Preprocessor& PP, PragmaIntroducer Introducer,
                        Token& PragmaTok) override {
        if (PragmaTok.isNot(tok::identifier)) {
          PP.Diag(PragmaTok, diag::warn_pragma_diagnostic_invalid);
          return;
        }
#ifndef NDEBUG
        IdentifierInfo* II = PragmaTok.getIdentifierInfo();
        assert(II->isStr("clad"));
#endif

        PP.Lex(PragmaTok);
        llvm::StringRef OptionName = PragmaTok.getIdentifierInfo()->getName();
        SourceLocation TokLoc = PragmaTok.getLocation();
        // Handle #pragma clad ON
        if (OptionName == "ON") {
          SourceRange R(TokLoc, /*end*/ SourceLocation());
          // If a second ON is seen, ignore it if the interval is open.
          if (CladEnabledRange.empty() ||
              CladEnabledRange.back().getEnd().isValid())
            CladEnabledRange.push_back(R);
          return;
        }
        // Handle #pragma clad OFF/DEFAULT
        if (OptionName == "OFF" || OptionName == "DEFAULT") {
          if (!CladEnabledRange.empty()) {
            assert(CladEnabledRange.back().getEnd().isInvalid());
            CladEnabledRange.back().setEnd(TokLoc);
          }
          return;
        }
        // Handle #pragma clad checkpoint loop
        if (OptionName == "checkpoint") {
          PP.Lex(PragmaTok);
          // Ensure the next token is `loop`
          if (PragmaTok.isNot(tok::identifier) ||
              PragmaTok.getIdentifierInfo()->getName() != "loop") {
            PP.Diag(PragmaTok.getLocation(),
                    PP.getDiagnostics().getCustomDiagID(
                        DiagnosticsEngine::Error,
                        "expected 'loop' after 'checkpoint' in #pragma clad"));
            return;
          }
          CladLoopCheckpoints.insert(PragmaTok.getLocation());
          return;
        }
        // Diagnose unknown clad pragma option
        PP.Diag(
            TokLoc,
            PP.getDiagnostics().getCustomDiagID(
                DiagnosticsEngine::Error,
                "expected 'ON', 'OFF', 'DEFAULT', or `checkpoint` in pragma"));
      }
    };

    CladPlugin::CladPlugin(CompilerInstance& CI, DifferentiationOptions& DO)
        : m_CI(CI), m_DO(DO), m_HasRuntime(false) {
      CodeGenOptions& CGOpts = m_CI.getCodeGenOpts();
      bool WantTiming = CGOpts.TimePasses;

      if (WantTiming || getenv("CLAD_ENABLE_TIMING"))
        InitTimers();

        // Register clad as a backend pass via the path of clad.so itself,
        // resolved from any symbol we own. Cleaner than iterating
        // CI.getFrontendOpts().Plugins (which depends on how clang was
        // invoked) and keeps the lookup inside this DSO.
#ifdef CLAD_BUILD_STATIC_ONLY
        // Skip registration entirely if clad is statically linked
#elif _WIN32
      HMODULE hm = nullptr;
      if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS |
                                 GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
                             reinterpret_cast<LPCSTR>(&InitTimers), &hm) &&
          hm) {
        char buf[MAX_PATH];
        if (DWORD n = GetModuleFileNameA(hm, buf, MAX_PATH);
            n > 0 && n < MAX_PATH)
          CGOpts.PassPlugins.emplace_back(buf);
      }
#else
      if (Dl_info info;
          dladdr(reinterpret_cast<void*>(&InitTimers), &info) && info.dli_fname)
        CGOpts.PassPlugins.emplace_back(info.dli_fname);
#endif

      // Add define for __CLAD__, so that CladFunction::CladFunction()
      // doesn't throw an error.
      auto predefines = m_CI.getPreprocessor().getPredefines();
      predefines.append("#define __CLAD__ 1\n");
      m_CI.getPreprocessor().setPredefines(predefines);
    }

    CladPlugin::~CladPlugin() {}

    ALLOW_ACCESS(MultiplexConsumer, Consumers,
                 std::vector<std::unique_ptr<ASTConsumer>>);

    void CladPlugin::Initialize(clang::ASTContext& C) {
      // We know we have a multiplexer. We commit a sin here by stealing it and
      // making the consumer pass-through so that we can delay all operations
      // until clad is happy.

      auto& MultiplexC = cast<MultiplexConsumer>(m_CI.getASTConsumer());
      auto& RobbedCs = ACCESS(MultiplexC, Consumers);
      assert(RobbedCs.back().get() == this && "Clad is not the last consumer");

      const auto& Macros = m_CI.getPreprocessorOpts().Macros;
      const bool IsCling = llvm::any_of(
          Macros, [](const auto& Macro) { return Macro.first == "__CLING__"; });
      if (IsCling && m_CI.getPreprocessor().isIncrementalProcessingEnabled()) {
        std::swap(RobbedCs.front(), RobbedCs.back());
        return;
      }
      std::vector<std::unique_ptr<ASTConsumer>> StolenConsumers;

      // The range-based for loop in MultiplexConsumer::Initialize has
      // dispatched this call. Generally, it is unsafe to delete elements while
      // iterating but we know we are in the end of the loop and ::end() won't
      // be invalidated.
      std::move(RobbedCs.begin(), RobbedCs.end() - 1,
                std::back_inserter(StolenConsumers));
      RobbedCs.erase(RobbedCs.begin(), RobbedCs.end() - 1);
      m_Multiplexer.reset(new MultiplexConsumer(std::move(StolenConsumers)));
    }

    void CladPlugin::HandleTopLevelDeclForClad(DeclGroupRef DGR) {
      if (!CheckBuiltins())
        return;
#if CLANG_VERSION_MAJOR > 16
      // Traverse all constexpr FunctionDecls for the static graph only once to
      // differentiate them immeditely.
      {
        TimedAnalysisRegion R("Rest of constexpr TU");
        for (Decl* D : DGR) {
          if (!isa<FunctionDecl>(D))
            continue;
          auto* FD = cast<FunctionDecl>(D);
          if (FD->isConstexpr() || !m_Multiplexer) {
            getScheduler().Plan(DGR);
            break;
          }
        }
      }

      // This handler can be re-entered while a planning traversal is on the
      // stack: a lookup issued by the traversal makes the ASTReader
      // deserialize pending module decls and pass them to the consumers. The
      // Plan call above then defers the group; processing requests here would
      // interleave with the outer traversal (and clobber its current
      // processing node), so leave them to the outer caller.
      if (!getScheduler().isTraversalInFlight())
        for (DiffRequest& request : getScheduler().getGraph().getNodes()) {
          if (request.ImmediateMode && request.Function->isConstexpr()) {
            getScheduler().getGraph().setCurrentProcessingNode(request);
            ProcessDiffRequest(request);
            getScheduler().getGraph().markCurrentNodeProcessed();
          }
        }
#endif

      // We could not delay the processing of derivatives, act as if each
      // call is final. That would still have vgvassilev/clad#248 unresolved.
      // Not on re-entry (see above): the outer traversal finalizes.
      if (!m_CI.getDiagnostics().hasErrorOccurred() &&
          !getScheduler().isTraversalInFlight() && !m_Multiplexer)
        FinalizeTranslationUnit();
    }

    static void printDerivative(clang::Decl* D, bool DeclarationOnly,
                                const DifferentiationOptions& DO) {
      clang::LangOptions LangOpts;
      LangOpts.CPlusPlus = true;
      clang::PrintingPolicy Policy(LangOpts);
      Policy.Bool = true;

      // if enabled, print source code of the derivatives
      if (DO.DumpDerivedFn) {
        D->print(llvm::outs(), Policy);
        if (DeclarationOnly)
          llvm::outs() << ";\n";
      }

      // if enabled, print ASTs of the derivatives
      if (DO.DumpDerivedAST)
        D->dumpColor();

      // if enabled, print the derivatives in a file
      if (DO.GenerateSourceFile) {
        std::error_code err;
        llvm::raw_fd_ostream f("Derivatives.cpp", err,
                               CLAD_COMPAT_llvm_sys_fs_Append);
        D->print(f, Policy);
        if (DeclarationOnly)
          f << ";\n";
        f.flush();
      }
    }

    class AttachedLoopStmtFinder
        : public RecursiveASTVisitor<AttachedLoopStmtFinder> {
      SourceLocation m_PragmaLoc;
      SourceManager& m_SM;
      Stmt* m_AttachedStmt = nullptr;
      SourceLocation m_AttachedLoopLoc;

    public:
      AttachedLoopStmtFinder(SourceLocation pragmaLoc, SourceManager& SM)
          : m_PragmaLoc(pragmaLoc), m_SM(SM) {}

      bool VisitStmt(Stmt* S) {
        SourceLocation beginLoc = S->getBeginLoc();
        if (!beginLoc.isValid() ||
            !m_SM.isBeforeInTranslationUnit(m_PragmaLoc, beginLoc))
          return true;

        if (!m_AttachedStmt || m_SM.isBeforeInTranslationUnit(
                                   beginLoc, m_AttachedStmt->getBeginLoc())) {
          m_AttachedStmt = S;
          m_AttachedLoopLoc = {};
          if (isa<ForStmt>(S) || isa<WhileStmt>(S) || isa<DoStmt>(S))
            m_AttachedLoopLoc = beginLoc;
        }
        return true;
      }

      [[nodiscard]] SourceLocation getAttachedLoopLoc() const {
        return m_AttachedLoopLoc;
      }

      [[nodiscard]] Stmt* getAttachedLoop() const {
        return m_AttachedLoopLoc.isValid() ? m_AttachedStmt : nullptr;
      }
    };

    /// Collects every variable declared inside the given statement.
    class LoopLocalDeclCollector
        : public RecursiveASTVisitor<LoopLocalDeclCollector> {
      llvm::SmallPtrSetImpl<const VarDecl*>& m_Decls;

    public:
      LoopLocalDeclCollector(llvm::SmallPtrSetImpl<const VarDecl*>& decls)
          : m_Decls(decls) {}
      bool VisitVarDecl(VarDecl* VD) {
        m_Decls.insert(VD);
        return true;
      }
    };

    /// Decides whether a loop marked with `#pragma clad checkpoint loop` can
    /// be checkpointed, and what the reverse sweep must do to recompute the
    /// loop's per-iteration state.
    ///
    /// Checkpointing replaces per-iteration tape stores with recomputation:
    /// the reverse sweep re-executes the (transformed) loop body to
    /// re-establish the values its pullbacks need. That only reproduces
    /// iteration i if everything the body reads is loop-invariant, derived
    /// from the loop counter, or restored first. Variables declared outside
    /// the loop but written inside it ("carried" variables) are none of
    /// those: their value at iteration i depends on the preceding
    /// iterations. When such a value is needed by the reverse sweep, the
    /// loop-entry state has to be saved and iterations 0..i-1 replayed
    /// (NeedsReplay). Writes the replay cannot redo faithfully -- through
    /// pointers, to globals, past a break -- make the loop unsupported, and
    /// it falls back to tape stores.
    class CheckpointLoopAnalyzer {
      // SetVectors keep the insertion order so the generated save/restore
      // statements are deterministic.
      llvm::SmallSetVector<const VarDecl*, 8> m_Written;
      llvm::SmallPtrSet<const VarDecl*, 8> m_InductionWritten;
      llvm::SmallPtrSet<const VarDecl*, 8> m_Demanded;
      llvm::SmallPtrSet<const VarDecl*, 16> m_LoopLocals;
      const char* m_Unsupported = nullptr;
      bool m_InInduction = false;

      void markUnsupported(const char* why) {
        if (!m_Unsupported)
          m_Unsupported = why;
      }

      static const VarDecl* getReferencedVarDecl(const Expr* E) {
        E = E->IgnoreParenImpCasts();
        if (const auto* DRE = dyn_cast<DeclRefExpr>(E))
          return dyn_cast<VarDecl>(DRE->getDecl());
        return nullptr;
      }

      /// Records a write to the lvalue `lhs`. `demandsOldValue` is true when
      /// the reverse sweep needs the overwritten value (e.g. `*=`).
      void analyzeWrite(const Expr* lhs, bool demandsOldValue) {
        lhs = lhs->IgnoreParenImpCasts();
        if (const VarDecl* VD = getReferencedVarDecl(lhs)) {
          if (!VD->hasLocalStorage()) {
            markUnsupported("the loop writes to a global variable");
            return;
          }
          if (m_InInduction)
            m_InductionWritten.insert(VD);
          else
            m_Written.insert(VD);
          if (demandsOldValue)
            m_Demanded.insert(VD);
          return;
        }
        // Writes through subscripts, members, or dereferences: fine if the
        // written object is a loop-local aggregate (replay re-creates it),
        // opaque otherwise.
        const Expr* base = lhs;
        while (true) {
          base = base->IgnoreParenImpCasts();
          if (const auto* ASE = dyn_cast<ArraySubscriptExpr>(base)) {
            analyzeReads(ASE->getIdx());
            base = ASE->getBase();
          } else if (const auto* ME = dyn_cast<MemberExpr>(base)) {
            base = ME->getBase();
          } else {
            break;
          }
        }
        if (const VarDecl* baseVD = getReferencedVarDecl(base))
          if (m_LoopLocals.contains(baseVD))
            return;
        markUnsupported("the loop writes through a pointer, array, or member "
                        "that is not local to the loop");
      }

      /// Every variable mentioned in `E` whose value the reverse sweep may
      /// need. Also rejects constructs that could modify state the replay
      /// does not restore.
      void analyzeReads(const Expr* E) {
        if (!E)
          return;
        E = E->IgnoreParenImpCasts();
        if (const auto* DRE = dyn_cast<DeclRefExpr>(E)) {
          if (const auto* VD = dyn_cast<VarDecl>(DRE->getDecl()))
            if (VD->hasLocalStorage())
              m_Demanded.insert(VD);
          return;
        }
        if (const auto* UO = dyn_cast<UnaryOperator>(E)) {
          if (UO->getOpcode() == UO_AddrOf) {
            markUnsupported("the loop takes the address of a variable");
            return;
          }
          if (UO->isIncrementDecrementOp()) {
            analyzeWrite(UO->getSubExpr(), /*demandsOldValue=*/true);
            return;
          }
        }
        if (const auto* BO = dyn_cast<BinaryOperator>(E)) {
          if (BO->isAssignmentOp()) {
            // An assignment in read position: its value is used, so the old
            // LHS value may be needed regardless of the operator.
            analyzeWrite(BO->getLHS(),
                         /*demandsOldValue=*/BO->isCompoundAssignmentOp());
            analyzeReads(BO->getRHS());
            return;
          }
        }
        if (const auto* CE = dyn_cast<CallExpr>(E)) {
          const FunctionDecl* callee = CE->getDirectCallee();
          for (unsigned i = 0, e = CE->getNumArgs(); i != e; ++i) {
            const Expr* arg = CE->getArg(i);
            QualType paramTy;
            if (callee && i < callee->getNumParams())
              paramTy = callee->getParamDecl(i)->getType();
            bool mayWriteThroughArg =
                arg->getType()->isPointerType() ||
                (!paramTy.isNull() && paramTy->isReferenceType() &&
                 !paramTy.getNonReferenceType().isConstQualified());
            if (mayWriteThroughArg) {
              markUnsupported("the loop passes a pointer or mutable reference "
                              "to a function");
              return;
            }
            analyzeReads(arg);
          }
          if (const auto* MCE = dyn_cast<CXXMemberCallExpr>(CE))
            if (MCE->getImplicitObjectArgument() &&
                getReferencedVarDecl(MCE->getImplicitObjectArgument())) {
              markUnsupported("the loop calls a member function on a "
                              "variable");
              return;
            }
          return;
        }
        for (const Stmt* child : E->children())
          if (const auto* childE = dyn_cast_or_null<Expr>(child))
            analyzeReads(childE);
      }

      /// An expression in statement position: its value is discarded, which
      /// makes `+=`/`-=` writes cheap -- their pullbacks never need the old
      /// left-hand side.
      void analyzeTopLevelExpr(const Expr* E) {
        E = E->IgnoreParenImpCasts();
        if (const auto* BO = dyn_cast<BinaryOperator>(E)) {
          if (BO->isAssignmentOp()) {
            BinaryOperatorKind opc = BO->getOpcode();
            bool demandsOldValue = BO->isCompoundAssignmentOp() &&
                                   opc != BO_AddAssign && opc != BO_SubAssign;
            analyzeWrite(BO->getLHS(), demandsOldValue);
            analyzeReads(BO->getRHS());
            return;
          }
          if (BO->getOpcode() == BO_Comma) {
            analyzeTopLevelExpr(BO->getLHS());
            analyzeTopLevelExpr(BO->getRHS());
            return;
          }
        }
        if (const auto* UO = dyn_cast<UnaryOperator>(E))
          if (UO->isIncrementDecrementOp()) {
            analyzeWrite(UO->getSubExpr(), /*demandsOldValue=*/false);
            return;
          }
        analyzeReads(E);
      }

      /// The loop condition is evaluated neither by the reverse sweep nor by
      /// a replay (both are counter-driven), so its reads are free -- but its
      /// side effects would be lost.
      void analyzeCond(const Expr* cond) {
        if (!cond)
          return;
        struct WriteFinder : RecursiveASTVisitor<WriteFinder> {
          bool hasWrites = false;
          bool VisitBinaryOperator(BinaryOperator* BO) {
            hasWrites |= BO->isAssignmentOp();
            return !hasWrites;
          }
          bool VisitUnaryOperator(UnaryOperator* UO) {
            hasWrites |= UO->isIncrementDecrementOp();
            return !hasWrites;
          }
          bool VisitCallExpr(CallExpr* CE) {
            hasWrites = true; // conservatively
            return false;
          }
        } finder;
        finder.TraverseStmt(const_cast<Expr*>(cond));
        if (finder.hasWrites)
          markUnsupported("the loop condition has side effects");
      }

      void analyzeStmt(const Stmt* S) {
        if (!S || m_Unsupported)
          return;
        if (isa<NullStmt>(S))
          return;
        if (const auto* CS = dyn_cast<CompoundStmt>(S)) {
          for (const Stmt* child : CS->body())
            analyzeStmt(child);
          return;
        }
        if (const auto* DS = dyn_cast<DeclStmt>(S)) {
          for (const Decl* D : DS->decls())
            if (const auto* VD = dyn_cast<VarDecl>(D))
              if (const Expr* init = VD->getInit())
                analyzeReads(init);
          return;
        }
        if (const auto* IS = dyn_cast<IfStmt>(S)) {
          analyzeStmt(IS->getInit());
          analyzeReads(IS->getCond());
          analyzeStmt(IS->getThen());
          analyzeStmt(IS->getElse());
          return;
        }
        if (isa<ForStmt>(S) || isa<WhileStmt>(S) || isa<DoStmt>(S) ||
            isa<CXXForRangeStmt>(S)) {
          // Re-executing a transformed nested loop would advance its
          // iteration counter without its reverse sweep consuming it.
          markUnsupported("the loop contains a nested loop");
          return;
        }
        if (isa<BreakStmt>(S) || isa<ContinueStmt>(S) || isa<GotoStmt>(S) ||
            isa<ReturnStmt>(S) || isa<SwitchStmt>(S)) {
          markUnsupported("the loop body alters control flow");
          return;
        }
        if (const auto* E = dyn_cast<Expr>(S)) {
          analyzeTopLevelExpr(E);
          return;
        }
        markUnsupported("the loop body contains an unsupported statement");
      }

    public:
      void analyze(const Stmt* loop, LoopCheckpointInfo& info) {
        LoopLocalDeclCollector collector(m_LoopLocals);
        collector.TraverseStmt(const_cast<Stmt*>(loop));

        const Stmt* body = nullptr;
        if (const auto* FS = dyn_cast<ForStmt>(loop)) {
          if (const Stmt* init = FS->getInit()) {
            m_InInduction = true;
            if (const auto* initE = dyn_cast<Expr>(init))
              analyzeTopLevelExpr(initE);
            else
              analyzeStmt(init);
            m_InInduction = false;
          }
          analyzeCond(FS->getCond());
          if (const Expr* inc = FS->getInc()) {
            m_InInduction = true;
            analyzeTopLevelExpr(inc);
            m_InInduction = false;
          }
          body = FS->getBody();
        } else if (const auto* WS = dyn_cast<WhileStmt>(loop)) {
          analyzeCond(WS->getCond());
          body = WS->getBody();
        } else if (const auto* DS = dyn_cast<DoStmt>(loop)) {
          analyzeCond(DS->getCond());
          body = DS->getBody();
        }
        analyzeStmt(body);

        // The reverse sweep recovers a for-loop's induction variables by
        // inverting the increment, so they need neither saving nor replay --
        // unless the body also writes them.
        for (const VarDecl* VD : m_InductionWritten)
          if (m_Written.count(VD))
            markUnsupported("the loop variable is modified in the body");

        for (const VarDecl* VD : m_Written) {
          if (m_LoopLocals.contains(VD) || m_InductionWritten.count(VD))
            continue;
          if (!VD->getType()->isArithmeticType()) {
            markUnsupported("the loop writes a non-scalar variable declared "
                            "outside of it");
            break;
          }
          info.CarriedVars.push_back(VD);
          if (m_Demanded.count(VD))
            info.NeedsReplay = true;
        }
        info.Unsupported = m_Unsupported;
        if (m_Unsupported) {
          info.CarriedVars.clear();
          info.NeedsReplay = false;
        }
      }
    };

    static LoopCheckpointInfo getLoopCheckpointInfo(const FunctionDecl* FD,
                                                    SourceLocation pragmaLoc,
                                                    SourceManager& SM) {
      Stmt* body = FD->getBody();
      AttachedLoopStmtFinder finder(pragmaLoc, SM);
      finder.TraverseStmt(body);
      LoopCheckpointInfo info;
      info.LoopLoc = finder.getAttachedLoopLoc();
      if (Stmt* loop = finder.getAttachedLoop())
        CheckpointLoopAnalyzer().analyze(loop, info);
      return info;
    }

    static void addCladLoopCheckpoints(ASTContext& C, DiffRequest& request) {
      SourceRange range = request->getSourceRange();
      assert(range.isValid());
      SourceLocation begin = range.getBegin();
      SourceLocation end = range.getEnd();
      clang::SourceManager& SM = C.getSourceManager();
      auto it = CladLoopCheckpoints.upper_bound(begin);
      auto e = CladLoopCheckpoints.end();

      for (; it != e && SM.isBeforeInTranslationUnit(*it, end); ++it)
        request.m_CladLoopCheckpoints.emplace(
            *it, getLoopCheckpointInfo(request.Function, *it, SM));
    }

    static void diagnoseUnusedPragma(Sema& S, DiffRequest& request) {
      if (request.Mode != DiffMode::reverse &&
          request.Mode != DiffMode::pullback)
        return;

      static std::set<clang::SourceLocation> DiagnosedCladLoopCheckpoints;
      for (const auto& pair : request.m_CladLoopCheckpoints) {
        if (!pair.second.LoopLoc.isValid()) {
          if (!DiagnosedCladLoopCheckpoints.insert(pair.first).second)
            continue;
          unsigned diagID = S.Diags.getCustomDiagID(
              DiagnosticsEngine::Error,
              "'#pragma clad checkpoint loop' is only allowed before a loop");
          S.Diag(pair.first, diagID);
          continue;
        }
        if (pair.second.Unsupported) {
          if (!DiagnosedCladLoopCheckpoints.insert(pair.first).second)
            continue;
          unsigned diagID = S.Diags.getCustomDiagID(
              DiagnosticsEngine::Warning,
              "'#pragma clad checkpoint loop' ignored because %0; values "
              "will be stored instead");
          S.Diag(pair.first, diagID) << pair.second.Unsupported;
        }
      }
    }

    FunctionDecl* CladPlugin::ProcessDiffRequest(DiffRequest& request) {
      Sema& S = m_CI.getSema();
      if (!m_DerivativeBuilder)
        m_DerivativeBuilder =
            std::make_unique<DerivativeBuilder>(S, *this, getScheduler());

      if (request.Global) {
        auto deriveResult = m_DerivativeBuilder->Derive(request);
        auto* VDDiff = cast_or_null<VarDecl>(deriveResult.derivative);
        ProcessTopLevelDecl(VDDiff);
        // Dump the declaration if requested.
        printDerivative(VDDiff, request.DeclarationOnly, m_DO);
        return nullptr;
      }

      if (request.Function->getDefinition())
        request.Function = request.Function->getDefinition();
      // FIXME: These requests are not fully generated in the diffplanner and we
      // have to update diff params on this stage.
      if (request.CurrentDerivativeOrder > 1 ||
          getScheduler().getDerivedFns().IsCladDerivative(request.Function))
        request.UpdateDiffParamsInfo(m_CI.getSema());
      const FunctionDecl* FD = request.Function;
      ASTContext& C = S.getASTContext();
      clang::PrintingPolicy Policy = C.getPrintingPolicy();
#if CLANG_VERSION_MAJOR > 10
      // Our testsuite expects 'a<b<c> >' rather than 'a<b<c>>'.
      Policy.SplitTemplateClosers = true;
#endif
      // if enabled, print source code of the original functions
      if (m_DO.DumpSourceFn) {
        FD->print(llvm::outs(), Policy);
      }
      // if enabled, print ASTs of the original functions
      if (m_DO.DumpSourceFnAST)
        FD->dumpColor();

      // If enabled, set the proper fields in derivative builder.
      if (m_DO.PrintNumDiffErrorInfo) {
        m_DerivativeBuilder->setNumDiffErrDiag(true);
      }

      // Propagate relevant pragmas to diffrequests
      addCladLoopCheckpoints(C, request);

      FunctionDecl* DerivativeDecl = nullptr;
      bool alreadyDerived = false;
      FunctionDecl* OverloadedDerivativeDecl = nullptr;
      {
        llvm::SaveAndRestore<unsigned> Saved(request.RequestedDerivativeOrder,
                                             1);
        auto DFI = getScheduler().getDerivedFns().Find(request);
        if (DFI.IsValid()) {
          DerivativeDecl = DFI.DerivedFn();
          OverloadedDerivativeDecl = DFI.OverloadedDerivedFn();
          alreadyDerived = true;
        } else {
          auto deriveResult = m_DerivativeBuilder->Derive(request);
          DerivativeDecl = cast_or_null<FunctionDecl>(deriveResult.derivative);
          OverloadedDerivativeDecl = deriveResult.overload;
          // FIXME: Doing this with other function types might lead to
          // accidental numerical diff.
          if (isa<CXXConstructorDecl>(FD) &&
              (request.Mode == DiffMode::pullback) &&
              utils::hasEmptyBody(DerivativeDecl))
            return nullptr;
          if (DerivativeDecl)
            getScheduler().getDerivedFns().Add(DerivedFnInfo(
                request, DerivativeDecl, OverloadedDerivativeDecl));
        }
      }

      // Propagate relevant pragmas to diffrequests
      diagnoseUnusedPragma(S, request);

      if (OverloadedDerivativeDecl) {
        S.MarkFunctionReferenced(SourceLocation(), OverloadedDerivativeDecl);
        DelayedCallInfo DCI{CallKind::HandleTopLevelDecl,
                            OverloadedDerivativeDecl};
        if (!llvm::is_contained(m_DelayedCalls, DCI))
          ProcessTopLevelDecl(OverloadedDerivativeDecl);
      }
      if (DerivativeDecl) {
        if (!alreadyDerived &&
            (!request.CustomDerivative || request.CallUpdateRequired)) {
          printDerivative(DerivativeDecl, request.DeclarationOnly, m_DO);

          S.MarkFunctionReferenced(SourceLocation(), DerivativeDecl);
          // We ideally should not call `HandleTopLevelDecl` for declarations
          // inside a namespace. After parsing a namespace that is defined
          // directly in translation unit context , clang calls
          // `BackendConsumer::HandleTopLevelDecl`.
          // `BackendConsumer::HandleTopLevelDecl` emits LLVM IR of each
          // declaration inside the namespace using CodeGen. We need to manually
          // call `HandleTopLevelDecl` for each new declaration added to a
          // namespace because `HandleTopLevelDecl` has already been called for
          // a namespace by Clang when the namespace is parsed.

          // Call CodeGen only if the produced Decl is a top-most
          // decl or is contained in a namespace decl.
          // FIXME: We could get rid of this by prepending the produced
          // derivatives in CladPlugin::HandleTranslationUnitDecl
          DeclContext* derivativeDC = DerivativeDecl->getLexicalDeclContext();
          DelayedCallInfo DCI{CallKind::HandleTopLevelDecl, DerivativeDecl};
          bool isTUorND =
              derivativeDC->isTranslationUnit() || derivativeDC->isNamespace();
          if (isTUorND && !llvm::is_contained(m_DelayedCalls, DCI))
            ProcessTopLevelDecl(DerivativeDecl);
        }
        bool lastDerivativeOrder = (request.CurrentDerivativeOrder ==
                                    request.RequestedDerivativeOrder);
        // If this is the last required derivative order, replace the function
        // inside a call to clad::differentiate/gradient with its derivative.
        if (request.CallUpdateRequired && lastDerivativeOrder)
          request.updateCall(DerivativeDecl, OverloadedDerivativeDecl,
                             m_CI.getSema());

        if (request.DeclarationOnly)
          request.DerivedFDPrototypes.push_back(DerivativeDecl);

        // Last requested order was computed, return the result.
        if (lastDerivativeOrder)
          return DerivativeDecl;
        // If higher order derivatives are required, proceed to compute them
        // recursively.
        request.Function = DerivativeDecl;
        request.CurrentDerivativeOrder += 1;
        return ProcessDiffRequest(request);
      }
      return nullptr;
    }

    void CladPlugin::SendToMultiplexer() {
      if (!m_Multiplexer)
        return;
      for (unsigned i = m_MultiplexerProcessedDelayedCallsIdx;
           i < m_DelayedCalls.size(); ++i) {
        auto DelayedCall = m_DelayedCalls[i];
        DeclGroupRef& D = DelayedCall.m_DGR;
        switch (DelayedCall.m_Kind) {
        case CallKind::HandleCXXStaticMemberVarInstantiation:
          m_Multiplexer->HandleCXXStaticMemberVarInstantiation(
              cast<VarDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleTopLevelDecl:
          m_Multiplexer->HandleTopLevelDecl(D);
          break;
        case CallKind::HandleInlineFunctionDefinition:
          m_Multiplexer->HandleInlineFunctionDefinition(
              cast<FunctionDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleInterestingDecl:
          m_Multiplexer->HandleInterestingDecl(D);
          break;
        case CallKind::HandleTagDeclDefinition:
          m_Multiplexer->HandleTagDeclDefinition(
              cast<TagDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleTagDeclRequiredDefinition:
          m_Multiplexer->HandleTagDeclRequiredDefinition(
              cast<TagDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleCXXImplicitFunctionInstantiation:
          m_Multiplexer->HandleCXXImplicitFunctionInstantiation(
              cast<FunctionDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleTopLevelDeclInObjCContainer:
          m_Multiplexer->HandleTopLevelDeclInObjCContainer(D);
          break;
        case CallKind::HandleImplicitImportDecl:
          m_Multiplexer->HandleImplicitImportDecl(
              cast<ImportDecl>(D.getSingleDecl()));
          break;
        case CallKind::CompleteTentativeDefinition:
          m_Multiplexer->CompleteTentativeDefinition(
              cast<VarDecl>(D.getSingleDecl()));
          break;
        case CallKind::CompleteExternalDeclaration:
          m_Multiplexer->CompleteExternalDeclaration(
              cast<VarDecl>(D.getSingleDecl()));
          break;
        case CallKind::AssignInheritanceModel:
          m_Multiplexer->AssignInheritanceModel(
              cast<CXXRecordDecl>(D.getSingleDecl()));
          break;
        case CallKind::HandleVTable:
          m_Multiplexer->HandleVTable(cast<CXXRecordDecl>(D.getSingleDecl()));
          break;
        case CallKind::InitializeSema:
          m_Multiplexer->InitializeSema(m_CI.getSema());
          break;
        };
      }

      m_MultiplexerProcessedDelayedCallsIdx = m_DelayedCalls.size();
    }

    bool CladPlugin::CheckBuiltins() {
      // If we have included "clad/Differentiator/Differentiator.h" return.
      if (m_HasRuntime)
        return true;

      // The plugin has a lot of different ways to be compiled: in-tree,
      // out-of-tree and hybrid. When we pick up the wrong header files we
      // usually see a problem with C.Idents not being properly initialized.
      // This assert tries to catch such situations heuristically.
      assert(&m_CI.getASTContext().Idents ==
                 &m_CI.getPreprocessor().getIdentifierTable() &&
             "Miscompiled?");
      NamespaceDecl* CladNS =
          utils::LookupNSD(m_CI.getSema(), "clad", /*shouldExist=*/false);
      m_HasRuntime = (CladNS != nullptr);
      return m_HasRuntime;
    }

    static void SetTBRAnalysisOptions(const DifferentiationOptions& DO,
                                      RequestOptions& opts) {
      // If user has explicitly specified the mode for TBR analysis, use it.
      if (DO.EnableTBRAnalysis || DO.DisableTBRAnalysis)
        opts.EnableTBRAnalysis = DO.EnableTBRAnalysis && !DO.DisableTBRAnalysis;
      else
        opts.EnableTBRAnalysis = true; // Default mode.
    }

    static void SetActivityAnalysisOptions(const DifferentiationOptions& DO,
                                           RequestOptions& opts) {
      // If user has explicitly specified the mode for AA, use it.
      if (DO.EnableVariedAnalysis || DO.DisableVariedAnalysis)
        opts.EnableVariedAnalysis =
            DO.EnableVariedAnalysis && !DO.DisableVariedAnalysis;
      else
        opts.EnableVariedAnalysis = false; // Default mode.
    }

    static void SetUsefulAnalysisOptions(const DifferentiationOptions& DO,
                                         RequestOptions& opts) {
      // If user has explicitly specified the mode for TBR analysis, use it.
      if (DO.EnableUsefulAnalysis || DO.DisableUsefulAnalysis)
        opts.EnableUsefulAnalysis =
            DO.EnableUsefulAnalysis && !DO.DisableUsefulAnalysis;
      else
        opts.EnableUsefulAnalysis = false; // Default mode.
    }
    void CladPlugin::SetRequestOptions(RequestOptions& opts) const {
      SetTBRAnalysisOptions(m_DO, opts);
      SetActivityAnalysisOptions(m_DO, opts);
      SetUsefulAnalysisOptions(m_DO, opts);
      opts.EmitPortingHints = m_DO.EmitPortingHints;
    }

    DiffScheduler& CladPlugin::getScheduler() {
      if (!m_Scheduler) {
        RequestOptions Opts{};
        SetRequestOptions(Opts);
        m_Scheduler = std::make_unique<DiffScheduler>(m_CI.getSema(), Opts,
                                                      CladEnabledRange);
      }
      return *m_Scheduler;
    }

    void CladPlugin::FinalizeTranslationUnit() {
      Sema& S = m_CI.getSema();
      // Restore the TUScope that became a 0 in Sema::ActOnEndOfTranslationUnit.
      if (!m_CI.getPreprocessor().isIncrementalProcessingEnabled())
        S.TUScope = m_StoredTUScope;
      constexpr bool Enabled = true;
      Sema::GlobalEagerInstantiationScope GlobalInstantiations(
          S, Enabled CLAD_COMPAT_CLANG21_AtEndOfTUParam);
      Sema::LocalEagerInstantiationScope LocalInstantiations(
          S CLAD_COMPAT_CLANG21_AtEndOfTUParam);

      if (!getScheduler().getGraph().isProcessingNode()) {
        // This check is to avoid recursive processing of the graph, as
        // HandleTopLevelDecl can be called recursively in non-standard
        // setup for code generation.
        DiffRequest request = getScheduler().getGraph().getNextToProcessNode();
        while (request.Function || request.Global) {
          getScheduler().getGraph().setCurrentProcessingNode(request);
          ProcessDiffRequest(request);
          getScheduler().getGraph().markCurrentNodeProcessed();
          request = getScheduler().getGraph().getNextToProcessNode();
        }
      }

      // Put the TUScope in a consistent state after clad is done.
      if (!m_CI.getPreprocessor().isIncrementalProcessingEnabled())
        S.TUScope = nullptr;

      // Force emission of the produced pending template instantiations.
      LocalInstantiations.perform();
      GlobalInstantiations.perform();
    }

    void CladPlugin::HandleTranslationUnit(ASTContext& C) {
      // In case of diagnostics, don't bother, just let the compiler finish.
      if (!m_CI.getDiagnostics().hasErrorOccurred()) {
        // Traverse all collected DeclGroupRef only once to create the static
        // graph. Planning can trigger implicit instantiations (e.g. clad::Tag
        // when parsing the differentiate-call arguments) whose consumer
        // notifications append to m_DelayedCalls mid-loop; deque::push_back
        // keeps element references valid but invalidates iterators, so index
        // instead of iterating (the appended groups are then planned too).
        // NOLINTNEXTLINE(modernize-loop-convert)
        for (size_t i = 0; i < m_DelayedCalls.size(); ++i) {
          const DelayedCallInfo DCI = m_DelayedCalls[i];
          for (Decl* D : DCI.m_DGR) {
            if (const auto* FD = dyn_cast<FunctionDecl>(D))
              if (FD->isConstexpr())
                continue;
            getScheduler().Plan(DCI.m_DGR);
            break;
          }
        }

        if (m_CI.getFrontendOpts().ShowStats) {
          // Print the graph of the diff requests.
          llvm::errs() << "\n*** INFORMATION ABOUT THE DIFF REQUESTS\n";
          getScheduler().getGraph().dump();
        }

        FinalizeTranslationUnit();
        SendToMultiplexer();
      }
      if (m_Multiplexer)
        m_Multiplexer->HandleTranslationUnit(C);
    }

    void CladPlugin::PrintStats() {
      llvm::errs() << "*** INFORMATION ABOUT THE DELAYED CALLS\n";
      for (const DelayedCallInfo& DCI : m_DelayedCalls) {
        llvm::errs() << "   ";
        switch (DCI.m_Kind) {
        case CallKind::HandleCXXStaticMemberVarInstantiation:
          llvm::errs() << "HandleCXXStaticMemberVarInstantiation";
          break;
        case CallKind::HandleTopLevelDecl:
          llvm::errs() << "HandleTopLevelDecl";
          break;
        case CallKind::HandleInlineFunctionDefinition:
          llvm::errs() << "HandleInlineFunctionDefinition";
          break;
        case CallKind::HandleInterestingDecl:
          llvm::errs() << "HandleInterestingDecl";
          break;
        case CallKind::HandleTagDeclDefinition:
          llvm::errs() << "HandleTagDeclDefinition";
          break;
        case CallKind::HandleTagDeclRequiredDefinition:
          llvm::errs() << "HandleTagDeclRequiredDefinition";
          break;
        case CallKind::HandleCXXImplicitFunctionInstantiation:
          llvm::errs() << "HandleCXXImplicitFunctionInstantiation";
          break;
        case CallKind::HandleTopLevelDeclInObjCContainer:
          llvm::errs() << "HandleTopLevelDeclInObjCContainer";
          break;
        case CallKind::HandleImplicitImportDecl:
          llvm::errs() << "HandleImplicitImportDecl";
          break;
        case CallKind::CompleteTentativeDefinition:
          llvm::errs() << "CompleteTentativeDefinition";
          break;
        case CallKind::CompleteExternalDeclaration:
          llvm::errs() << "CompleteExternalDeclaration";
          break;
        case CallKind::AssignInheritanceModel:
          llvm::errs() << "AssignInheritanceModel";
          break;
        case CallKind::HandleVTable:
          llvm::errs() << "HandleVTable";
          break;
        case CallKind::InitializeSema:
          llvm::errs() << "InitializeSema";
          break;
        };
        for (const clang::Decl* D : DCI.m_DGR) {
          llvm::errs() << " " << D;
          if (const auto* ND = dyn_cast<NamedDecl>(D))
            llvm::errs() << " " << ND->getNameAsString();
        }
        llvm::errs() << "\n";
      }

      if (m_Multiplexer)
        m_Multiplexer->PrintStats();
    }

  } // end namespace plugin

  // Routine to check clang version at runtime against the clang version for
  // which clad was built.
  bool checkClangVersion() {
    std::string runtimeVersion = clang::getClangFullCPPVersion();
    std::string builtVersion = CLANG_MAJOR_VERSION;
    if (runtimeVersion.find(builtVersion) == std::string::npos)
      return false;
    else
      return true;
  }
} // end namespace clad

// Attach the frontend plugin.

using namespace clad::plugin;
// register the PluginASTAction in the registry.
static clang::FrontendPluginRegistry::Add<Action<CladPlugin> >
X("clad", "Produces derivatives or arbitrary functions");

static PragmaHandlerRegistry::Add<CladPragmaHandler>
    Y("clad", "Clad pragma directives handler.");

// Attach the backend plugin.
#include "ClangBackendPlugin.h"

#define BACKEND_PLUGIN_NAME "CladBackendPlugin"
// FIXME: Add a proper versioning that's based on CLANG_VERSION_STRING and
// a similar approach for clad (see Version.cpp and VERSION).
#define BACKEND_PLUGIN_VERSION "FIXME"
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, BACKEND_PLUGIN_NAME, BACKEND_PLUGIN_VERSION,
          clad::ClangBackendPluginPass::registerCallbacks};
}
