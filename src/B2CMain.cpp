#include <iostream>
#include <map>
#include <stack>
#include <vector>
#include <string>
#include "antlr4-runtime.h"
#include "antlr4-cpp/BBaseVisitor.h"
#include "antlr4-cpp/BLexer.h"
#include "antlr4-cpp/BParser.h"

using namespace std;
using namespace antlr4;
using namespace antlr4::tree;

enum Types {tyAUTO, tyINT, tyDOUBLE, tySTRING, tyBOOL, tyCHAR, tyFUNCTION, tyVOID, tyMACRO};
string mnemonicTypes[] = {"auto", "int", "double", "string", "bool", "char", "function", "void", "macro"};

void print_error_and_exit(int lineNum, const string& errorMsg) {
    cerr << "Error at line " << lineNum << ": " << errorMsg << endl;
    exit(-1);
}

struct SymbolAttributes {
    Types type;
    vector<Types> retArgTypes;
};

class SymbolTable {
private:
    map<string, SymbolAttributes> table;
public:
    void addSymbol(const string& name, const SymbolAttributes& attributes) { table[name] = attributes; }
    bool symbolExists(const string& name) const { return table.find(name) != table.end(); }
    SymbolAttributes getSymbolAttributes(const string& name) const {
        if (symbolExists(name)) return table.at(name);
        else { cout << "Error: Symbol " << name << " not found" << endl; exit(-1); }
    }
    void removeSymbol(const string& name) { table.erase(name); }
    const map<string, SymbolAttributes>& getSymbols() const { return table; }
};

const string _GlobalFuncName_ = "$_global_$";
map<string, SymbolTable*> symTabs;

// --- Global State for PA#2 ---
map<ParseTree*, string> nodeScopeMap;
map<string, string> parentScopeMap;
map<string, vector<string>> functionParamNames;
map<string, bool> definedFunctionNames;
map<string, bool> functionHasReturn;

string findSymbolScope(string currentScope, const string& name) {
    while (currentScope != "") {
        if (symTabs.count(currentScope) && symTabs[currentScope]->symbolExists(name)) return currentScope;
        if (parentScopeMap.count(currentScope)) currentScope = parentScopeMap[currentScope];
        else break;
    }
    return "";
}

// --- STEP 1 ---
class SymbolTableVisitor : public BBaseVisitor {
private:
    stack<string> scopeStack;
    map<string, int> childBlockCount;
    bool isFunctionBody = false;

    string getCurrentScope() { return scopeStack.top(); }
    void pushScope(string scopeName, ParseTree* ctx = nullptr) {
        string parent = scopeStack.empty() ? "" : scopeStack.top();
        scopeStack.push(scopeName);
        if (symTabs.find(scopeName) == symTabs.end()) symTabs[scopeName] = new SymbolTable();
        if (!parent.empty() && scopeName != _GlobalFuncName_) parentScopeMap[scopeName] = parent;
        if (ctx) nodeScopeMap[ctx] = scopeName;
    }
    void popScope() { scopeStack.pop(); }

public:
    any visitProgram(BParser::ProgramContext *ctx) override {
        pushScope(_GlobalFuncName_, ctx);
        for (auto child : ctx->children) visit(child);
        popScope();
        return nullptr;
    }
    any visitDeclstmt(BParser::DeclstmtContext *ctx) override {
        string funcName = ctx->name()->getText();
        SymbolTable* globalTab = symTabs[_GlobalFuncName_];
        int declSigSize = ctx->AUTO().size();

        if (globalTab->symbolExists(funcName)) {
            SymbolAttributes existingAttr = globalTab->getSymbolAttributes(funcName);
            if (existingAttr.type != tyFUNCTION || existingAttr.retArgTypes.size() != declSigSize) {
                print_error_and_exit(ctx->getStart()->getLine(), "Multiple definition of '" + funcName + "'");
            }
        } else {
            SymbolAttributes attr; attr.type = tyFUNCTION;
            for (int i = 0; i < declSigSize; i++) attr.retArgTypes.push_back(tyAUTO);
            globalTab->addSymbol(funcName, attr);
        }
        return nullptr;
    }
    any visitFuncdef(BParser::FuncdefContext *ctx) override {
        string funcName = ctx->name(0)->getText();
        SymbolTable* globalTab = symTabs[_GlobalFuncName_];
        int defSigSize = ctx->name().size();

        if (definedFunctionNames[funcName]) {
            print_error_and_exit(ctx->getStart()->getLine(), "Multiple definition of '" + funcName + "'");
        }

        if (globalTab->symbolExists(funcName)) {
            SymbolAttributes existingAttr = globalTab->getSymbolAttributes(funcName);
            if (existingAttr.type != tyFUNCTION || existingAttr.retArgTypes.size() != defSigSize) {
                print_error_and_exit(ctx->getStart()->getLine(), "Multiple definition of '" + funcName + "'");
            }
        } else {
            SymbolAttributes attr; attr.type = tyFUNCTION;
            for(int i = 0; i < defSigSize; i++) attr.retArgTypes.push_back(tyAUTO);
            globalTab->addSymbol(funcName, attr);
        }

        definedFunctionNames[funcName] = true;
        pushScope(funcName, ctx);
        SymbolTable* funcTab = symTabs[funcName];

        for(int i = 1; i < ctx->name().size(); i++) {
            string paramName = ctx->name(i)->getText();
            if (funcTab->symbolExists(paramName)) {
                print_error_and_exit(ctx->name(i)->getStart()->getLine(), "Multiple definition of parameter");
            }
            funcTab->addSymbol(paramName, {tyAUTO});
            functionParamNames[funcName].push_back(paramName);
        }

        isFunctionBody = true;
        visit(ctx->blockstmt());
        popScope();
        return nullptr;
    }
    any visitBlockstmt(BParser::BlockstmtContext *ctx) override {
        bool createdNewScope = false;
        if (isFunctionBody) { isFunctionBody = false; nodeScopeMap[ctx] = getCurrentScope(); }
        else {
            createdNewScope = true;
            string parentScope = getCurrentScope();
            childBlockCount[parentScope]++;
            string newScopeName = parentScope + (parentScope.find('$') == string::npos ? "_$" : "_") + to_string(childBlockCount[parentScope]);
            pushScope(newScopeName, ctx);
        }
        for (auto stmt : ctx->statement()) visit(stmt);
        if (createdNewScope) popScope();
        return nullptr;
    }
    any visitAutostmt(BParser::AutostmtContext *ctx) override {
        string currentScope = getCurrentScope();
        SymbolTable *stab = symTabs[currentScope];
        for (int i = 0; i < ctx->children.size(); i++) {
            if (auto nameCtx = dynamic_cast<BParser::NameContext*>(ctx->children[i])) {
                string varName = nameCtx->getText();
                if (stab->symbolExists(varName)) print_error_and_exit(nameCtx->getStart()->getLine(), "Multiple definition");
                stab->addSymbol(varName, {tyAUTO});
            }
        }
        return nullptr;
    }
};

// --- STEP 2.1 PrePass ---
class FunctionCallPrePassVisitor : public BBaseVisitor {
private:
    stack<string> scopeStack;
    string getCurrentScope() { return scopeStack.top(); }
    void pushScope(ParseTree* ctx) {
        if (nodeScopeMap.count(ctx)) scopeStack.push(nodeScopeMap[ctx]);
        else if (!scopeStack.empty()) scopeStack.push(scopeStack.top());
        else scopeStack.push(_GlobalFuncName_);
    }
    void popScope() { scopeStack.pop(); }
public:
    any visitProgram(BParser::ProgramContext *ctx) override { pushScope(ctx); for(auto c : ctx->children) visit(c); popScope(); return nullptr; }
    any visitFuncdef(BParser::FuncdefContext *ctx) override { pushScope(ctx); visit(ctx->blockstmt()); popScope(); return nullptr; }
    any visitBlockstmt(BParser::BlockstmtContext *ctx) override { pushScope(ctx); for(auto s : ctx->statement()) visit(s); popScope(); return nullptr; }

    any visitAutostmt(BParser::AutostmtContext *ctx) override {
        for (int i = 0, j = 0; i < ctx->name().size(); i++) {
            string varName = ctx->name(i)->getText();
            int idx_assn = 1 + i*2 + j*2 + 1;
            if (idx_assn < ctx->children.size() && ctx->children[idx_assn]->getText() == "=") {
                if (ctx->constant(j)) {
                    Types constType = any_cast<Types>(visit(ctx->constant(j)));
                    string targetScope = findSymbolScope(getCurrentScope(), varName);
                    if (targetScope != "") {
                        SymbolAttributes attr = symTabs[targetScope]->getSymbolAttributes(varName);
                        if (attr.type == tyAUTO) { attr.type = constType; symTabs[targetScope]->addSymbol(varName, attr); }
                    }
                    j++;
                }
            }
        }
        return nullptr;
    }
    any visitFuncinvocation(BParser::FuncinvocationContext *ctx) override {
        string funcName = ctx->name()->getText();
        int lineNum = ctx->getStart()->getLine();
        if (!symTabs[_GlobalFuncName_]->symbolExists(funcName)) {
            for (auto e : ctx->expr()) visit(e);
            return tyMACRO;
        }
        SymbolAttributes funcAttr = symTabs[_GlobalFuncName_]->getSymbolAttributes(funcName);
        int argCount = ctx->expr().size();
        if (funcAttr.retArgTypes.size() - 1 != argCount) print_error_and_exit(lineNum, "Argument count mismatch in pre-pass");

        for (int i = 0; i < argCount; i++) {
            Types argType = any_cast<Types>(visit(ctx->expr(i)));
            int paramIdx = i + 1;
            if (funcAttr.retArgTypes[paramIdx] == tyAUTO && argType != tyAUTO && argType != tyMACRO) {
                funcAttr.retArgTypes[paramIdx] = argType;
                if (symTabs.count(funcName)) {
                    string pName = functionParamNames[funcName][i];
                    SymbolAttributes localAttr = symTabs[funcName]->getSymbolAttributes(pName);
                    localAttr.type = argType;
                    symTabs[funcName]->addSymbol(pName, localAttr);
                }
            }
        }
        symTabs[_GlobalFuncName_]->addSymbol(funcName, funcAttr);
        return funcAttr.retArgTypes[0];
    }
    any visitExpression(BParser::ExpressionContext *ctx) override {
        Types rhsType = any_cast<Types>(visit(ctx->expr()));
        if (ctx->ASSN()) {
            string varName = ctx->name()->getText();
            string targetScope = findSymbolScope(getCurrentScope(), varName);
            if (targetScope != "") {
                SymbolAttributes attr = symTabs[targetScope]->getSymbolAttributes(varName);
                if (attr.type == tyAUTO && rhsType != tyMACRO) { attr.type = rhsType; symTabs[targetScope]->addSymbol(varName, attr); }
            }
        }
        return rhsType;
    }
    any visitExpr(BParser::ExprContext *ctx) override {
        if (ctx->atom()) {
            Types t = any_cast<Types>(visit(ctx->atom()));
            if (ctx->NOT()) return tyBOOL;
            if (ctx->PLUS() || ctx->MINUS()) return t;
            return t;
        }
        if (ctx->QUEST()) {
            visit(ctx->expr(0));
            Types t1 = any_cast<Types>(visit(ctx->expr(1)));
            Types t2 = any_cast<Types>(visit(ctx->expr(2)));
            return t1 != tyMACRO ? t1 : t2;
        }

        Types leftType = any_cast<Types>(visit(ctx->expr(0)));
        Types rightType = any_cast<Types>(visit(ctx->expr(1)));

        if (ctx->GT() || ctx->GTE() || ctx->LT() || ctx->LTE() || ctx->EQ() || ctx->NEQ() || ctx->AND() || ctx->OR()) return tyBOOL;

        if (leftType == tyDOUBLE || rightType == tyDOUBLE) return tyDOUBLE;
        return leftType != tyMACRO ? leftType : rightType;
    }
    any visitAtom(BParser::AtomContext *ctx) override {
        if (ctx->expression()) return visit(ctx->expression());
        return visit(ctx->children[0]);
    }
    any visitConstant(BParser::ConstantContext *ctx) override {
        if (ctx->INT()) return tyINT; else if (ctx->REAL()) return tyDOUBLE; else if (ctx->STRING()) return tySTRING; else if (ctx->BOOL()) return tyBOOL; else if (ctx->CHAR()) return tyCHAR;
        return tyAUTO;
    }
    any visitName(BParser::NameContext *ctx) override {
        string targetScope = findSymbolScope(getCurrentScope(), ctx->getText());
        if (targetScope != "") return symTabs[targetScope]->getSymbolAttributes(ctx->getText()).type;
        return tyAUTO;
    }
};

// --- STEP 2.2 Full Analysis ---
class TypeAnalysisVisitor : public BBaseVisitor {
public:
    bool isStrictPass = false;
private:
    stack<string> scopeStack;
    string currentFunctionName = "";

    string getCurrentScope() { return scopeStack.top(); }
    void pushScope(ParseTree* ctx) {
        if (nodeScopeMap.count(ctx)) scopeStack.push(nodeScopeMap[ctx]);
        else if (!scopeStack.empty()) scopeStack.push(scopeStack.top());
        else scopeStack.push(_GlobalFuncName_);
    }
    void popScope() { scopeStack.pop(); }

public:
    any visitProgram(BParser::ProgramContext *ctx) override { pushScope(ctx); for(auto c : ctx->children) visit(c); popScope(); return nullptr; }
    any visitFuncdef(BParser::FuncdefContext *ctx) override {
        pushScope(ctx);
        string prevFunc = currentFunctionName;
        currentFunctionName = ctx->name(0)->getText();
        functionHasReturn[currentFunctionName] = false;
        visit(ctx->blockstmt());
        currentFunctionName = prevFunc;
        popScope();
        return nullptr;
    }
    any visitBlockstmt(BParser::BlockstmtContext *ctx) override { pushScope(ctx); for(auto s : ctx->statement()) visit(s); popScope(); return nullptr; }

    any visitExpression(BParser::ExpressionContext *ctx) override {
        Types rhsType = any_cast<Types>(visit(ctx->expr()));
        if (ctx->ASSN()) {
            string varName = ctx->name()->getText();
            int lineNum = ctx->name()->getStart()->getLine();
            string targetScope = findSymbolScope(getCurrentScope(), varName);

            if (targetScope != "") {
                SymbolAttributes attr = symTabs[targetScope]->getSymbolAttributes(varName);
                if (attr.type == tyAUTO) {
                    if (rhsType != tyMACRO && rhsType != tyAUTO) {
                        attr.type = rhsType;
                        symTabs[targetScope]->addSymbol(varName, attr);
                    }
                } else if (attr.type != rhsType && rhsType != tyMACRO) {
                    if (rhsType == tyAUTO && !isStrictPass) { /* Relaxed pass ignores */ }
                    else print_error_and_exit(lineNum, "Type mismatch in assignment");
                }
            } else {
                print_error_and_exit(lineNum, "Undefined variable: " + varName);
            }
        }
        return rhsType;
    }

    any visitReturnstmt(BParser::ReturnstmtContext *ctx) override {
        int lineNum = ctx->getStart()->getLine();
        Types retType = tyVOID;
        functionHasReturn[currentFunctionName] = true;

        if (ctx->expression()) retType = any_cast<Types>(visit(ctx->expression()));

        if (currentFunctionName != "") {
            SymbolAttributes funcAttr = symTabs[_GlobalFuncName_]->getSymbolAttributes(currentFunctionName);
            if (funcAttr.retArgTypes[0] == tyAUTO) {
                if (retType != tyAUTO && retType != tyMACRO) {
                    funcAttr.retArgTypes[0] = retType;
                    symTabs[_GlobalFuncName_]->addSymbol(currentFunctionName, funcAttr);
                }
            } else if (funcAttr.retArgTypes[0] != retType) {
                if (retType == tyAUTO && !isStrictPass) { /* Relaxed */ }
                else print_error_and_exit(lineNum, "Inconsistent return types");
            }
        }
        return nullptr;
    }

    any visitFuncinvocation(BParser::FuncinvocationContext *ctx) override {
        string funcName = ctx->name()->getText();
        int lineNum = ctx->getStart()->getLine();

        if (!symTabs[_GlobalFuncName_]->symbolExists(funcName)) {
            for (auto e : ctx->expr()) visit(e);
            return tyMACRO;
        }

        SymbolAttributes funcAttr = symTabs[_GlobalFuncName_]->getSymbolAttributes(funcName);
        int argCount = ctx->expr().size();

        if (funcAttr.retArgTypes.size() - 1 != argCount) print_error_and_exit(lineNum, "Argument count mismatch");

        for (int i = 0; i < argCount; i++) {
            Types argType = any_cast<Types>(visit(ctx->expr(i)));
            int paramIdx = i + 1;

            if (funcAttr.retArgTypes[paramIdx] == tyAUTO) {
                if (argType != tyAUTO && argType != tyMACRO) {
                    funcAttr.retArgTypes[paramIdx] = argType;
                    if (symTabs.count(funcName)) {
                        string pName = functionParamNames[funcName][i];
                        SymbolAttributes localAttr = symTabs[funcName]->getSymbolAttributes(pName);
                        localAttr.type = argType;
                        symTabs[funcName]->addSymbol(pName, localAttr);
                    }
                }
            } else if (funcAttr.retArgTypes[paramIdx] != argType && argType != tyMACRO) {
                if (argType == tyAUTO && !isStrictPass) { /* Relaxed */ }
                else print_error_and_exit(lineNum, "Parameter type mismatch");
            }
        }
        symTabs[_GlobalFuncName_]->addSymbol(funcName, funcAttr);
        return funcAttr.retArgTypes[0];
    }

    any visitExpr(BParser::ExprContext *ctx) override {
        int lineNum = ctx->getStart()->getLine();
        if (ctx->atom()) {
            Types t = any_cast<Types>(visit(ctx->atom()));
            if (ctx->NOT()) {
                if (t != tyBOOL && t != tyMACRO) {
                    if (t == tyAUTO && !isStrictPass) return tyAUTO;
                    print_error_and_exit(lineNum, "Logical NOT needs bool");
                }
                return tyBOOL;
            }
            if (ctx->PLUS() || ctx->MINUS()) {
                if (t != tyINT && t != tyDOUBLE && t != tyMACRO) {
                    if (t == tyAUTO && !isStrictPass) return tyAUTO;
                    print_error_and_exit(lineNum, "Unary +/- needs numeric type");
                }
                return t;
            }
            return t;
        }
        if (ctx->QUEST()) {
            Types condType = any_cast<Types>(visit(ctx->expr(0)));
            Types t1 = any_cast<Types>(visit(ctx->expr(1)));
            Types t2 = any_cast<Types>(visit(ctx->expr(2)));
            if (condType != tyBOOL && condType != tyMACRO && condType != tyAUTO) print_error_and_exit(lineNum, "Condition must be bool");
            if (t1 != t2 && t1 != tyMACRO && t2 != tyMACRO && t1 != tyAUTO && t2 != tyAUTO) print_error_and_exit(lineNum, "Ternary mismatch");
            return t1 != tyMACRO ? t1 : t2;
        }

        Types leftType = any_cast<Types>(visit(ctx->expr(0)));
        Types rightType = any_cast<Types>(visit(ctx->expr(1)));

        if (leftType == tyAUTO || rightType == tyAUTO) {
            if (isStrictPass) print_error_and_exit(lineNum, "Unresolved auto type in expression");
            return tyAUTO;
        }

        bool isMacroAssoc = (leftType == tyMACRO || rightType == tyMACRO);

        if (ctx->GT() || ctx->GTE() || ctx->LT() || ctx->LTE() || ctx->EQ() || ctx->NEQ()) {
            if (!isMacroAssoc && leftType != rightType) {
                if (!((leftType == tyINT && rightType == tyDOUBLE) || (leftType == tyDOUBLE && rightType == tyINT))) {
                    print_error_and_exit(lineNum, "Type mismatch in relational op");
                }
            }
            return tyBOOL;
        }
        if (ctx->AND() || ctx->OR()) {
            if (!isMacroAssoc && (leftType != tyBOOL || rightType != tyBOOL)) print_error_and_exit(lineNum, "Logical op needs bool");
            return tyBOOL;
        }
        if (ctx->PLUS() || ctx->MINUS() || ctx->MUL() || ctx->DIV()) {
            if (isMacroAssoc) return leftType != tyMACRO ? leftType : rightType;
            if (leftType == rightType) return leftType;
            if ((leftType == tyINT && rightType == tyDOUBLE) ||
                (leftType == tyDOUBLE && rightType == tyINT)) {
                return tyDOUBLE;
            }
            print_error_and_exit(lineNum, "Type mismatch in arithmetic op");
            return tyAUTO;
        }
        return tyAUTO;
    }

    any visitAtom(BParser::AtomContext *ctx) override {
        if (ctx->expression()) return visit(ctx->expression());
        return visit(ctx->children[0]);
    }
    any visitConstant(BParser::ConstantContext *ctx) override {
        if (ctx->INT()) return tyINT; else if (ctx->REAL()) return tyDOUBLE; else if (ctx->STRING()) return tySTRING; else if (ctx->BOOL()) return tyBOOL; else if (ctx->CHAR()) return tyCHAR;
        return tyAUTO;
    }
    any visitName(BParser::NameContext *ctx) override {
        string targetScope = findSymbolScope(getCurrentScope(), ctx->getText());
        if (targetScope != "") return symTabs[targetScope]->getSymbolAttributes(ctx->getText()).type;
        return tyAUTO;
    }
};

// --- Global Finalization & Checks ---
void finalizeVoidReturnTypes() {
    for (const auto& pair : symTabs[_GlobalFuncName_]->getSymbols()) {
        string funcName = pair.first;
        if (pair.second.type == tyFUNCTION && definedFunctionNames[funcName] && !functionHasReturn[funcName]) {
            SymbolAttributes attr = pair.second;
            if (attr.retArgTypes[0] == tyAUTO) {
                attr.retArgTypes[0] = tyVOID;
                symTabs[_GlobalFuncName_]->addSymbol(funcName, attr);
            }
        }
    }
}

void checkUnresolvedTypes() {
    for (const auto& tabPair : symTabs) {
        for (const auto& symPair : tabPair.second->getSymbols()) {
            Types type = symPair.second.type;
            if (type == tyFUNCTION) {
                for (Types t : symPair.second.retArgTypes) {
                    if (t == tyAUTO || t == tyMACRO) {
                        cerr << "Error: Unresolved function return/parameter type for '" << symPair.first << "'" << endl;
                        exit(-1);
                    }
                }
            } else if (type == tyAUTO || type == tyMACRO) {
                cerr << "Error: Unresolved auto/macro type for variable '" << symPair.first << "'" << endl;
                exit(-1);
            }
        }
    }
}

// --- STEP 3 Print ---
class PrintTreeVisitor : public BBaseVisitor {
private:
    stack<string> scopeStack;
    string currentFunctionName = "";

    string getCurrentScope() { return scopeStack.top(); }
    void pushScope(ParseTree* ctx) {
        if (nodeScopeMap.count(ctx)) scopeStack.push(nodeScopeMap[ctx]);
        else if (!scopeStack.empty()) scopeStack.push(scopeStack.top());
        else scopeStack.push(_GlobalFuncName_);
    }
    void popScope() { scopeStack.pop(); }

    string getSafeTypeString(Types t, int lineNum) {
        if (t == tyAUTO || t == tyMACRO || t == tyFUNCTION) print_error_and_exit(lineNum, "Unresolved type at codegen");
        return mnemonicTypes[t];
    }

public:
    any visitProgram(BParser::ProgramContext *ctx) override { pushScope(ctx); for(auto c : ctx->children) visit(c); popScope(); return nullptr; }
    
    any visitDirective(BParser::DirectiveContext *ctx) override { cout << ctx->SHARP_DIRECTIVE()->getText() << endl; return nullptr; }
    any visitDefinition(BParser::DefinitionContext *ctx) override { visit(ctx->children[0]); return nullptr; }

    any visitFuncdef(BParser::FuncdefContext *ctx) override {
        pushScope(ctx);
        string prevFunc = currentFunctionName;
        currentFunctionName = ctx->name(0)->getText();
        int lineNum = ctx->getStart()->getLine();
        
        SymbolAttributes funcAttr = symTabs[_GlobalFuncName_]->getSymbolAttributes(currentFunctionName);
        Types retType = funcAttr.retArgTypes[0];
        if (currentFunctionName == "main" && retType != tyINT) retType = tyINT;

        cout << getSafeTypeString(retType, lineNum) << " " << currentFunctionName << "(";
        for (int i=1; i < ctx->name().size(); i++) {
            if (i != 1) cout << ", ";
            cout << getSafeTypeString(funcAttr.retArgTypes[i], lineNum) << " " << ctx->name(i)->getText();
        }
        cout << ")" << endl;

        visit(ctx->blockstmt());
        currentFunctionName = prevFunc;
        popScope();
        return nullptr;
    }

    any visitDeclstmt(BParser::DeclstmtContext *ctx) override {
        string funcName = ctx->name()->getText();
        int lineNum = ctx->getStart()->getLine();
        SymbolAttributes funcAttr = symTabs[_GlobalFuncName_]->getSymbolAttributes(funcName);
        
        cout << getSafeTypeString(funcAttr.retArgTypes[0], lineNum) << " " << funcName << "(";
        for (int i=1; i < funcAttr.retArgTypes.size(); i++) {
            if (i != 1) cout << ", ";
            cout << getSafeTypeString(funcAttr.retArgTypes[i], lineNum);
        }
        cout << ");" << endl;
        return nullptr;
    }

    any visitBlockstmt(BParser::BlockstmtContext *ctx) override { pushScope(ctx); cout << "{" << endl; for(auto s : ctx->statement()) visit(s); cout << "}" << endl; popScope(); return nullptr; }

    any visitAutostmt(BParser::AutostmtContext *ctx) override {
        for (int i = 0; i < ctx->children.size(); i++) {
            if (auto nameCtx = dynamic_cast<BParser::NameContext*>(ctx->children[i])) {
                string varName = nameCtx->getText();
                string targetScope = findSymbolScope(getCurrentScope(), varName);
                Types realType = symTabs[targetScope]->getSymbolAttributes(varName).type;
                
                cout << getSafeTypeString(realType, nameCtx->getStart()->getLine()) << " " << varName;
                
                if (i + 1 < ctx->children.size() && ctx->children[i+1]->getText() == "=") {
                    cout << " = ";
                    visit(ctx->children[i+2]);
                    i += 2;
                }
                cout << ";" << endl;
            }
        }
        return nullptr;
    }

    any visitStatement(BParser::StatementContext *ctx) override { visit(ctx->children[0]); return nullptr; }
    any visitIfstmt(BParser::IfstmtContext *ctx) override { cout << "if ("; visit(ctx->expr()); cout << ") "; visit(ctx->statement(0)); if (ctx->ELSE()) { cout << endl << "else "; visit(ctx->statement(1)); } return nullptr; }
    any visitWhilestmt(BParser::WhilestmtContext *ctx) override { cout << "while ("; visit(ctx->expr()); cout << ") "; visit(ctx->statement()); return nullptr; }
    any visitExpressionstmt(BParser::ExpressionstmtContext *ctx) override { visit(ctx->expression()); cout << ";" << endl; return nullptr; }
    
    any visitReturnstmt(BParser::ReturnstmtContext *ctx) override {
        cout << "return";
        if (ctx->expression()) {
            cout << " ";
            if (currentFunctionName == "main") { cout << "(int)("; visit(ctx->expression()); cout << ")"; }
            else { visit(ctx->expression()); }
        }
        cout << ";" << endl;
        return nullptr;
    }
    any visitNullstmt(BParser::NullstmtContext *ctx) override { cout << ";" << endl; return nullptr; }

    any visitExpression(BParser::ExpressionContext *ctx) override {
        if (ctx->ASSN()) {
            string varName = ctx->name()->getText();
            string targetScope = findSymbolScope(getCurrentScope(), varName);
            Types lhsType = symTabs[targetScope]->getSymbolAttributes(varName).type;

            visit(ctx->name()); cout << " = ";
            if (lhsType == tyCHAR) { cout << "(char)("; visit(ctx->expr()); cout << ")"; }
            else { visit(ctx->expr()); }
        } else { visit(ctx->expr()); }
        return nullptr;
    }

    any visitExpr(BParser::ExprContext *ctx) override {
        if(ctx->atom()) {
            if (ctx->PLUS()) cout << "+"; else if (ctx->MINUS()) cout << "-"; else if (ctx->NOT()) cout << "!";
            visit(ctx->atom()); 
        } else if (ctx->QUEST()) {
            visit(ctx->expr(0)); cout << " ? "; visit(ctx->expr(1)); cout << " : "; visit(ctx->expr(2));
        } else {
            visit(ctx->expr(0));
            cout << " " << ctx->children[1]->getText() << " ";
            visit(ctx->expr(1));
        }   
        return nullptr;
    }
    any visitAtom(BParser::AtomContext *ctx) override {
        if (ctx->expression()) { cout << "("; visit(ctx->expression()); cout << ")"; }
        else visit(ctx->children[0]);
        return nullptr;
    }
    any visitFuncinvocation(BParser::FuncinvocationContext *ctx) override {
        cout << ctx->name()->getText() << "(";
        for (int i=0; i < ctx->expr().size(); i++) { if (i != 0) cout << ", "; visit(ctx->expr(i)); }
        cout << ")";
        return nullptr;
    }
    any visitConstant(BParser::ConstantContext *ctx) override { cout << ctx->children[0]->getText(); return nullptr; }
    any visitName(BParser::NameContext *ctx) override { cout << ctx->NAME()->getText(); return nullptr; }
};

int main(int argc, const char* argv[]) {
    if (argc < 2) { cerr << "[Usage] " << argv[0] << " <input-file>\n"; exit(0); }
    std::ifstream stream; stream.open(argv[1]);
    if (stream.fail()) { cerr << argv[1] << " : file open fail\n"; exit(0); }

    ANTLRInputStream inputStream(stream);
    BLexer lexer(&inputStream);
    CommonTokenStream tokenStream(&lexer);
    BParser parser(&tokenStream);
    ParseTree* tree = parser.program();

    SymbolTableVisitor SymtabTree; SymtabTree.visit(tree);
    FunctionCallPrePassVisitor PrePassTree; PrePassTree.visit(tree);
    
    TypeAnalysisVisitor RelaxedAnalyzeTree; RelaxedAnalyzeTree.isStrictPass = false; RelaxedAnalyzeTree.visit(tree);
    finalizeVoidReturnTypes();
    
    TypeAnalysisVisitor StrictAnalyzeTree; StrictAnalyzeTree.isStrictPass = true; StrictAnalyzeTree.visit(tree);
    finalizeVoidReturnTypes();
    checkUnresolvedTypes();

    PrintTreeVisitor PrintTree; PrintTree.visit(tree);

    return 0;
}
