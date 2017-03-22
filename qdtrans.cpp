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
#include <fstream>
#include <sstream>

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
#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Twine.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;
using namespace clang::tooling;

ASTContext *LastContext;

SourceLocation *LastTranslationUnitLoc;

Replacement createAdjustedReplacementForCSR(CharSourceRange csr, ASTContext* TheContext, Replacements& reps, std::string text);

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
private:
    ASTContext *TheContext;
    Rewriter &TheRewriter;
    Replacements &TheReplacements;
public:
    MyASTVisitor(ASTContext *C, Rewriter &R, Replacements &Rp) : TheContext(C), TheRewriter(R), TheReplacements(Rp) {
        LastContext = TheContext;
    }

    bool VisitStmt(Stmt *s) {
        //std::cout << "VisitStmt()\n";
        Stmt::child_iterator ChildIterator = s->child_begin();
        Stmt::child_iterator AddNode = s->child_begin();
        bool inCrit = false;
        std::stringstream nodetext;
        std::string nodestring;
        llvm::raw_string_ostream os(nodestring);
        AddNode++;
        while(ChildIterator != s->child_end()) {
            //std::cout << "Iterated\n";
            if(inCrit == false) {
                if(isa<CallExpr>(*ChildIterator)) {
                    CallExpr* MyCallExpr = cast<CallExpr>(*ChildIterator);
                    FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                    if(MyFunDecl != 0) {
                        std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                        if(ChildIterator != s->child_end() && name == "pthread_mutex_lock") {
                            inCrit = true;
                            nodetext.str("");
                            nodestring = "";
                        }
                    }
                } else {
                    //std::cout << "Dumping:\n";
                    //Stmt* currs = *MyChildIterator;
                    //currs->dump();
                }
                AddNode++;
            } else {
                bool goelse = false;
                if(isa<CallExpr>(*ChildIterator)) {
                    CallExpr* MyCallExpr = cast<CallExpr>(*ChildIterator);
                    FunctionDecl* MyFunDecl = MyCallExpr->getDirectCallee();
                    if(MyFunDecl != 0) {
                        std::string name = MyFunDecl->getNameInfo().getName().getAsString();
                        if(ChildIterator != s->child_end() && name == "pthread_mutex_unlock") {
                            inCrit = false;
                            PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                            PrintingPolicy& ppr = pp;
                            (*AddNode)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                            nodetext << nodestring << "\n";
                            CharSourceRange csr = CharSourceRange::getCharRange((*AddNode)->getSourceRange());
                            Replacement rep = createAdjustedReplacementForCSR(csr, TheContext, TheReplacements, nodetext.str());
                            Replacement& repr = rep;
                            rep.apply(TheRewriter);
                            Replacements reps = Replacements(repr);
                            TheReplacements.merge(reps);
                        } else {
                            goelse = true;
                        }
                    } else {
                        goelse = true;
                    }
                } else {
                    goelse = true;
                }
                if(goelse == true) { //Deduplicated else section starts here
                    nodestring = "";
                    PrintingPolicy pp = PrintingPolicy(TheContext->getLangOpts());
                    PrintingPolicy& ppr = pp;
                    (*ChildIterator)->printPretty(os, (PrinterHelper*)NULL, ppr, (unsigned)4);
                    nodetext << nodestring << "\n";
                }
            }
            ChildIterator++;
        } 
        return true;
    }

    
    bool VisitDecl(Decl *d) {
        //std::cout << "ASDFASDF";
        if (isa<TranslationUnitDecl>(d)) {
            //d->dumpColor();
            SourceLocation sl = d->getLocation();
            LastTranslationUnitLoc = &sl;
        }
        return true;
    }
    
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(ASTContext *C, Rewriter &R, Replacements &Rp) : Visitor(C, R, Rp) {}

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
    Replacements &TheReplacements;
    Rewriter TheRewriter;
    std::string TheCode;
    SourceLocation TranslationUnitLoc;
public:
    MyASTClassAction(Replacements &Rp, std::string Code) : TheReplacements(Rp), TheCode(Code) {}
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        TheRewriter = Rewriter(Compiler.getASTContext().getSourceManager(), Compiler.getASTContext().getLangOpts());
        Rewriter &RwRef = TheRewriter;
        RewriteBuffer &RewriteBuf = TheRewriter.getEditBuffer(Compiler.getASTContext().getSourceManager().getMainFileID());
        // Somehow even initializing a buffer and then immediately attempting to print it causes a failed assertion. I can't even.
        RewriteBuf.Initialize(StringRef(TheCode));
        /*std::string resultstring;
        llvm::raw_string_ostream os(resultstring);
        RewriteBuf.write(os);
        std::cout << resultstring;*/
        return std::unique_ptr<clang::ASTConsumer>(new MyASTConsumer(&Compiler.getASTContext(), RwRef, TheReplacements));
    }

    Rewriter& getRewriter() {
        return TheRewriter;
    }
};

void printUsage() {
    std::cout << "\nUsage:\n\tqdtrans <single input file> [Clang options]\n\n";
}

Replacement createAdjustedReplacementForCSR(CharSourceRange csr, ASTContext* TheContext, Replacements& reps, std::string text) {
    SourceManager& sm = TheContext->getSourceManager();
    FullSourceLoc fslstart = FullSourceLoc(csr.getBegin(), sm);
    FullSourceLoc fslend = FullSourceLoc(csr.getBegin(), sm);
    unsigned start = std::get<1>(fslstart.getDecomposedLoc());
    unsigned length = std::get<1>(fslend.getDecomposedLoc())-start;
    Range range = Range(start, length);
    std::vector<Range> rangevecin(1);
    rangevecin[0] = range;   
    std::vector<Range> rangevecout = calculateRangesAfterReplacements(reps, rangevecin);
    Range adjrange = rangevecout[0];
    Replacement newReplacement = Replacement(sm.getFileEntryForID(sm.getMainFileID())->tryGetRealPathName(), adjrange.getOffset(), adjrange.getLength(), StringRef(text));
    return newReplacement;
}

int main(int argc, char **argv) {
    if (argc > 1) {
        if(strcmp(argv[1], "--help") == 0) {
            printUsage();
        } else {
            Replacements TheReplacements = Replacements();
            Replacements& Rp = TheReplacements;
            std::vector<std::string> args(argc-2);
            for(int i = 0; i < argc-2; i++) {
                args[i] = argv[i+2];
            }
            std::ifstream t(argv[1]);
            std::stringstream buffer;
            buffer << t.rdbuf();
            MyASTClassAction *maca = new MyASTClassAction(Rp, buffer.str());
            clang::tooling::runToolOnCodeWithArgs(maca, Twine(buffer.str()), args, Twine(argv[1]));
            //clang::tooling::runToolOnCode(new MyASTClassAction(Rp), argv[1]);
            //const RewriteBuffer &RewriteBuf = maca->getRewriter().getEditBuffer(LastContext->getSourceManager().getMainFileID());
            Rewriter &Rw = maca->getRewriter();
            std::string resultstring;
            //llvm::raw_string_ostream os(resultstring);
            //resultstring = Rw.getRewrittenText(SourceRange(LastContext->getTranslationUnitDecl()->getLocation()));
            resultstring = Rw.getRewrittenText(*LastTranslationUnitLoc);
            //RewriteBuf.write(os);
            std::cout << resultstring;
            //std::cout << std::string(RewriteBuf.begin(), RewriteBuf.end());
        }
    } else {
        printUsage();
    }
}
