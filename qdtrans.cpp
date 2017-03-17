//------------------------------------------------------------------------------
// Clang rewriter sample. Demonstrates:
//
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/Core/Replacement.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"

#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
// Declares llvm::cl::extrahelp.
#include "llvm/Support/CommandLine.h"

using namespace clang;
using namespace clang::tooling;

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
private:
    Rewriter &TheRewriter;
    Replacements &TheReplacements;
public:
    MyASTVisitor(Rewriter &R, Replacements &Rp) : TheRewriter(R), TheReplacements(Rp) {}

    bool VisitStmt(Stmt *s) {

        std::cout << "VisitStmt()\n";
        Stmt::child_iterator MyChildIterator = s->child_begin();
        while(MyChildIterator != s->child_end()) {
            std::cout << "Iterated\n";
            if (isa<CallExpr>(*MyChildIterator)) {
                CallExpr* MyCallExpr = cast<CallExpr>(*MyChildIterator);
                FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                if(MyFunDecl != 0) {
                    std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                    std::cout << name;
                }
            } else {
                std::cout << "Dumping:\n";
                Stmt* currs = *MyChildIterator;
                currs->dump();
            }
            MyChildIterator++;
        }
        return true;
    }

    bool VisitDecl(Decl *d) {
        //std::cout << "ASDFASDF";
        if (isa<TranslationUnitDecl>(d)) {
            d->dumpColor();
        }
        return true;
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(Rewriter &R, Replacements &Rp) : Visitor(R, Rp) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    // Traversing the translation unit decl via a RecursiveASTVisitor
    // will visit all nodes in the AST.
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }

private:
  MyASTVisitor Visitor;
};

using namespace llvm;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static llvm::cl::OptionCategory MyToolCategory("qdtrans options");

class MyASTClassAction : public clang::ASTFrontendAction {
private:
    Rewriter &TheRewriter;
    Replacements &TheReplacements;
public:
    MyASTClassAction(Rewriter &R, Replacements &Rp) : TheRewriter(R), TheReplacements(Rp) {}
    
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new MyASTConsumer(TheRewriter, TheReplacements));
  }
    
};

void printUsage() {
    std::cout << "\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n";
}

int main(int argc, char **argv) {
    if (argc > 1) {
        if(strcmp(argv[1], "--help") == 0) {
            printUsage();
        } else {
            Rewriter TheRewriter = Rewriter();
            Replacements TheReplacements = Replacements();
            Rewriter& Rw = TheRewriter;
            Replacements& Rp = TheReplacements;
            std::vector<std::string> args(argc-2);
            for(int i = 0; i < argc-2; i++) {
                args[i] = argv[i+2];
            }
            clang::tooling::runToolOnCodeWithArgs(new MyASTClassAction(Rw, Rp), argv[1], args);
            //clang::tooling::runToolOnCode(new MyASTClassAction(Rw, Rp), argv[1]);
        }
    } else {
        printUsage();
    }
}
