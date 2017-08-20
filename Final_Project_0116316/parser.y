%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "header.h"
#include "symtab.h"
#include "semcheck.h"

extern int linenum;
extern FILE	*yyin;
extern char	*yytext;
extern char buf[256];
extern int Opt_Symbol;		/* declared in lex.l */
extern int avaNum;

int counter = 1;
int Label = 0;
int Loop = 0;
int loopStack[256];
int stack = 95;
char test = 'a';
int idorder = 0;
int scope = 0;
int read = 0;
char fileName[256];
struct SymTable *symbolTable;
__BOOLEAN paramError;
struct PType *funcReturn;
struct PType *temp;
__BOOLEAN semError = __FALSE;
int inloop = 0;
FILE *output; 
int decl_flag = 0;

char GetType(struct PType *node){
	if(node->type == VOID_t)
		return 'V';
	else if(node->type == INTEGER_t)
		return 'I';
	else if(node->type == FLOAT_t)
		return 'F';
	else if(node->type == BOOLEAN_t)
		return 'Z';
	else if(node->type == STRING_t)
		return 'C';
	else if(node->type == FUNCTION_t)
		return 'U';
	else 
		return 'E';
}

%}

%union {
	int intVal;
	float floatVal;	
	char *lexeme;
	struct idNode_sem *id;
	struct ConstAttr *constVal;
	struct PType *ptype;
	struct param_sem *par;
	struct expr_sem *exprs;
	struct expr_sem_node *exprNode;
	struct constParam *constNode;
	struct varDeclParam* varDeclNode;
};

%token	LE_OP NE_OP GE_OP EQ_OP AND_OP OR_OP
%token	READ BOOLEAN WHILE DO IF ELSE TRUE FALSE FOR INT PRINT BOOL VOID FLOAT DOUBLE STRING CONTINUE BREAK RETURN CONST
%token	L_PAREN R_PAREN COMMA SEMICOLON ML_BRACE MR_BRACE L_BRACE R_BRACE ADD_OP SUB_OP MUL_OP DIV_OP MOD_OP ASSIGN_OP LT_OP GT_OP NOT_OP

%token <lexeme>ID
%token <intVal>INT_CONST 
%token <floatVal>FLOAT_CONST
%token <floatVal>SCIENTIFIC
%token <lexeme>STR_CONST

%type<ptype> scalar_type dim
%type<par> array_decl parameter_list
%type<constVal> literal_const
%type<constNode> const_list 
%type<exprs> variable_reference logical_expression logical_term logical_factor relation_expression arithmetic_expression term factor logical_expression_list literal_list initial_array
%type<intVal> relation_operator add_op mul_op dimension
%type<varDeclNode> identifier_list


%start program
%%

program :		
				{
					//Open the output file 
					char name[200];
					memset(name, 0, sizeof(name));
					strncpy(name, fileName, sizeof(fileName));
					char *sub = ".j";
					strncat(name, sub, 202);
					if(output = fopen(name, "w"))
						fprintf(stderr, "FILENAME:%s\n", name);
					else
						fprintf(stderr, "Failed:%s\n", name);
						
					fprintf(output, "; %s\n" ,name);			  
					fprintf(output, ".class public %s\n", fileName);
					fprintf(output, ".super java/lang/Object\n");
					fprintf(output, ".field public static _sc Ljava/util/Scanner;\n");
				}
				decl_list 
			    funct_def
				decl_and_def_list 
				{
					if(Opt_Symbol == 1)
					printSymTable( symbolTable, scope );	
					fclose(output);
				}
		;

decl_list : decl_list var_decl
		  | decl_list const_decl
		  | decl_list funct_decl
		  |
		  ;


decl_and_def_list : decl_and_def_list var_decl
				  | decl_and_def_list const_decl
				  | decl_and_def_list funct_decl
				  | decl_and_def_list funct_def
				  | 
				  ;

		  
funct_def : scalar_type ID L_PAREN R_PAREN 
			{
				int notmain = 1;
				char Name[256];
				memset(Name, 0, 256);
				strcpy(Name, $2);	
				notmain = strcmp(Name,"main");								
				
				funcReturn = $1; 
				struct SymNode *node;
				node = findFuncDeclaration( symbolTable, $2 );
				
				if(notmain != 0){  //not main function 
					if( node != 0 ){
						verifyFuncDeclaration(symbolTable, 0, $1, node );
					}
					else{
						insertFuncIntoSymTable(symbolTable, $2, 0, $1, scope, __TRUE);
					}
					
					fprintf(output, "\n.method public static %s(", $2);
					funcReturn = $1;
					fprintf(output, ")%c\n", GetType($1));
					fprintf(output, ".limit stack 100\n");
					fprintf(output, ".limit locals 100\n");						
				}
				else{  //main function must be void
					insertFuncIntoSymTable(symbolTable, $2, 0, createPType( VOID_t ) , scope, __TRUE);		
					funcReturn = createPType(VOID_t); 
					fprintf(output, ".method public static main([Ljava/lang/String;)V\n" );
					fprintf(output, "\t.limit stack 100\n");
					fprintf(output, "\t.limit locals 100\n");
					fprintf(output, "\tnew java/util/Scanner\n");
					fprintf(output, "\tdup\n");
					fprintf(output, "\tgetstatic java/lang/System/in Ljava/io/InputStream;\n");
					fprintf(output, "\tinvokespecial java/util/Scanner/<init>(Ljava/io/InputStream;)V\n");
					fprintf(output, "\tputstatic %s/_sc Ljava/util/Scanner;\n", fileName);				
				}
			}
			compound_statement{ 
						fprintf(output, ".end method\n");		
						funcReturn = 0; 
			}
		  | scalar_type ID L_PAREN parameter_list R_PAREN  
			{				
				fprintf(output, "\n.method public static %s(", $2);
				struct param_sem *node;
				node = $4;
				fprintf(output, "%c", GetType($1));
				for(node = node->next; node != 0; node = node->next){
					fprintf(output, ",%c", GetType($1));
				}
				
				funcReturn = $1;
				
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				// check and insert function into symbol table
				else{
					struct SymNode *node;
					node = findFuncDeclaration( symbolTable, $2 );

					if( node != 0 ){
						if(verifyFuncDeclaration( symbolTable, $4, $1, node ) == __TRUE){	
							insertParamIntoSymTable( symbolTable, $4, scope+1 );
						}				
					}
					else{
						insertParamIntoSymTable( symbolTable, $4, scope+1 );				
						insertFuncIntoSymTable( symbolTable, $2, $4, $1, scope, __TRUE );
					}
				}
				fprintf(output, ")%c\n", GetType($1));
				fprintf(output, ".limit stack 100\n");
				fprintf(output, ".limit locals 100\n");	
			} 	
			compound_statement {
				funcReturn = 0;
				fprintf(output, ".end method\n");
			}
		  | VOID ID L_PAREN R_PAREN 
			{
				funcReturn = createPType(VOID_t); 
				struct SymNode *node;
				node = findFuncDeclaration( symbolTable, $2 );

				if( node != 0 ){
					verifyFuncDeclaration( symbolTable, 0, createPType( VOID_t ), node );					
				}
				else{
					insertFuncIntoSymTable( symbolTable, $2, 0, createPType( VOID_t ), scope, __TRUE );	
				}
				fprintf( output, "\n.method public static %s(", $2 );
				funcReturn = 0;
				fprintf( output, ")%c\n", 'V' );
				fprintf( output, ".limit stack 100\n" );
				fprintf( output, ".limit locals 100\n" );		
			}
			compound_statement{
				funcReturn = 0;
				fprintf(output, "\treturn\n");
				fprintf(output, ".end method\n");
			}
		  | VOID ID L_PAREN parameter_list R_PAREN
			{						
				fprintf(output, "\n.method public static %s(", $2);
				struct param_sem *node;
				node = $4;
				fprintf(output, "%c", funcReturn);
				for(node = node->next; node != 0; node = node->next){
					fprintf(output, ",%c", funcReturn);
				}
				
				funcReturn = createPType(VOID_t);
				
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				// check and insert function into symbol table
				else{
					struct SymNode *node;
					node = findFuncDeclaration( symbolTable, $2 );

					if( node != 0 ){
						if(verifyFuncDeclaration( symbolTable, $4, createPType( VOID_t ), node ) == __TRUE){	
							insertParamIntoSymTable( symbolTable, $4, scope+1 );				
						}
					}
					else{
						insertParamIntoSymTable( symbolTable, $4, scope+1 );				
						insertFuncIntoSymTable( symbolTable, $2, $4, createPType( VOID_t ), scope, __TRUE );
					}
				}
				fprintf(output, ")%c\n", 'V');
				fprintf(output, ".limit stack 100\n");
				fprintf(output, ".limit locals 100\n");	
			} 
			compound_statement {
				funcReturn = 0;
				fprintf(output, "\treturn\n");
				fprintf(output, ".end method\n");
			}		  
		  ;

funct_decl : scalar_type ID L_PAREN R_PAREN SEMICOLON
			{
				insertFuncIntoSymTable( symbolTable, $2, 0, $1, scope, __FALSE );	
			}
		   | scalar_type ID L_PAREN parameter_list R_PAREN SEMICOLON
		    {
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				else {
					insertFuncIntoSymTable( symbolTable, $2, $4, $1, scope, __FALSE );
				}
			}
		   | VOID ID L_PAREN R_PAREN SEMICOLON
			{				
				insertFuncIntoSymTable( symbolTable, $2, 0, createPType( VOID_t ), scope, __FALSE );
			}
		   | VOID ID L_PAREN parameter_list R_PAREN SEMICOLON
			{
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;	
				}
				else {
					insertFuncIntoSymTable( symbolTable, $2, $4, createPType( VOID_t ), scope, __FALSE );
				}
			}
		   ;

parameter_list : parameter_list COMMA scalar_type ID
			   {
				/*struct param_sem *ptr1;
				ptr1 = $1;
				fprintf(output, "%c", GetType(ptr1->pType));
				for(ptr1 = $1->next; ptr1 != 0; ptr1 = (ptr1->next)){
					fprintf(output, "%c", GetType(ptr1->pType));
				}*/
			   
				struct param_sem *ptr;
				ptr = createParam( createIdList( $4 ), $3 );
				param_sem_addParam( $1, ptr );
				$$ = $1;
			   }
			   | parameter_list COMMA scalar_type array_decl
			   {
				$4->pType->type= $3->type;
				param_sem_addParam( $1, $4 );
				$$ = $1;
			   }
			   | scalar_type array_decl 
			   { 
				$2->pType->type = $1->type;  
				$$ = $2;
			   }
			   | scalar_type ID 
			   { 
				//fprintf(output, "\t%c", GetType($1));
				$$ = createParam( createIdList( $2 ), $1 );
				}
			   ;

var_decl : scalar_type identifier_list SEMICOLON
			{
				struct varDeclParam *ptr;
				struct SymNode *newNode;
				for( ptr=$2 ; ptr!=0 ; ptr=(ptr->next) ) {	
					
					if( verifyRedeclaration( symbolTable, ptr->para->idlist->value, scope ) == __FALSE ) {
						}
					else {
						//printf("%d\n", scope);
						if( verifyVarInitValue( $1, ptr, symbolTable, scope ) ==  __TRUE ){	
							newNode = createVarNode( ptr->para->idlist->value, scope, ptr->para->pType, ptr->order );
							insertTab( symbolTable, newNode );											
						}
						if(scope == 0){
							fprintf(output, ".field public static %s %c\n", ptr->para->idlist->value, GetType($1));
						}
					}
				}
			}
			;	

identifier_list : identifier_list COMMA ID
				{					
					struct param_sem *ptr;	
					struct varDeclParam *vptr;				
					ptr = createParam( createIdList( $3 ), createPType( VOID_t ) );
					if(scope == 0){
						idorder = 0;
						counter = 0;
					}
						
					else{
						counter++;
						idorder++;
						ptr->order = idorder;
					}
					vptr = createVarDeclParam( ptr, 0 );	
					addVarDeclParam( $1, vptr );
					$$ = $1; 					
				}
                | identifier_list COMMA ID ASSIGN_OP logical_expression
				{	
					fprintf(output, "\tistore %d\n", counter);
				
					struct param_sem *ptr;	
					struct varDeclParam *vptr;				
					ptr = createParam( createIdList( $3 ), createPType( VOID_t ) );
					if(scope == 0){
						counter = 0;
						idorder = 0;
					}
					else{
						idorder++;
						counter++;
						//printf("%d\n", idorder);
						ptr->order = idorder;
						//printf("%d\n", ptr->order);
					}
					vptr = createVarDeclParam( ptr, $5 );
					vptr->isArray = __TRUE;
					vptr->isInit = __TRUE;	
					addVarDeclParam( $1, vptr );	
					$$ = $1;
					/*
					struct SymNode *node;
					node = lookupSymbol( symbolTable, $3, scope, __FALSE);
						
					if(node->scope == 0){
						if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
							fprintf(output, "\tputstatic %s/%s I\n", fileName, $3);
						else
							fprintf(output, "\tputstatic %s/%s F\n", fileName, $3);
					}
					else{
						if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
							fprintf(output, "\tistore %d\n", node->order);
						else
							fprintf(output, "\tfstore %d\n", node->order);
					}	*/				
				}
                | identifier_list COMMA array_decl ASSIGN_OP initial_array
				{
					struct varDeclParam *ptr;
					ptr = createVarDeclParam( $3, $5 );
					ptr->isArray = __TRUE;
					ptr->isInit = __TRUE;
					addVarDeclParam( $1, ptr );
					$$ = $1;	
				}
                | identifier_list COMMA array_decl
				{
					struct varDeclParam *ptr;
					ptr = createVarDeclParam( $3, 0 );
					ptr->isArray = __TRUE;
					addVarDeclParam( $1, ptr );
					$$ = $1;
				}
                | array_decl ASSIGN_OP initial_array
				{	
					$$ = createVarDeclParam( $1 , $3 );
					$$->isArray = __TRUE;
					$$->isInit = __TRUE;	
				}
                | array_decl 
				{ 
					$$ = createVarDeclParam( $1 , 0 ); 
					$$->isArray = __TRUE;
				}
                | ID ASSIGN_OP logical_expression
				{
					fprintf(output, "\tistore %d\n", counter);
					
					struct param_sem *ptr;					
					ptr = createParam( createIdList( $1 ), createPType( VOID_t ) );
					if(scope == 0){
						counter = 0;
						idorder = 0;
					}
					else{
						idorder++;
						counter++;
						//printf("%d\n", idorder);
						ptr->order = idorder;
						//printf("%d\n", ptr->order);
					}
					$$ = createVarDeclParam( ptr, $3 );		
					$$->isInit = __TRUE;
					/*
					struct SymNode *node;
					node = lookupSymbol( symbolTable, $1, scope, __FALSE);
				
					if(node->scope == 0){
						if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
							fprintf(output, "\tputstatic %s/%s I\n", fileName, $1);
						else
							fprintf(output, "\tputstatic %s/%s F\n", fileName, $1);
					}
					else{
						if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
							fprintf(output, "\tistore %d\n", node->order);
						else
							fprintf(output, "\tfstore %d\n", node->order);
					}*/		
				}
                | ID 
				{
					struct param_sem *ptr;					
					ptr = createParam( createIdList( $1 ), createPType( VOID_t ) );
					if(scope == 0){
						idorder = 0;
						counter = 0;
					}
						
					else{
						idorder++;
						counter++;
						ptr->order = idorder;
					}
					$$ = createVarDeclParam( ptr, 0 );				
				}
                ;
		 
initial_array : L_BRACE literal_list R_BRACE { $$ = $2; }
			  ;

literal_list : literal_list COMMA logical_expression
				{
					struct expr_sem *ptr;
					for( ptr=$1; (ptr->next)!=0; ptr=(ptr->next) );				
					ptr->next = $3;
					$$ = $1;
				}
             | logical_expression
				{
					$$ = $1;
				}
             ;

const_decl 	: CONST scalar_type const_list SEMICOLON
			{
				struct SymNode *newNode;				
				struct constParam *ptr;
				for( ptr=$3; ptr!=0; ptr=(ptr->next) ){
					if( verifyRedeclaration( symbolTable, ptr->name, scope ) == __TRUE ){//no redeclare
						if( ptr->value->category != $2->type ){//type different
							if( !(($2->type==FLOAT_t || $2->type == DOUBLE_t ) && ptr->value->category==INTEGER_t) ) {
								if(!($2->type==DOUBLE_t && ptr->value->category==FLOAT_t)){	
									fprintf( stdout, "########## Error at Line#%d: const type different!! ##########\n", linenum );
									semError = __TRUE;	
								}
								else{
									newNode = createConstNode( ptr->name, scope, $2, ptr->value );
									insertTab( symbolTable, newNode );
								}
							}							
							else{
								newNode = createConstNode( ptr->name, scope, $2, ptr->value );
								insertTab( symbolTable, newNode );
							}
						}
						else{
							newNode = createConstNode( ptr->name, scope, $2, ptr->value );
							insertTab( symbolTable, newNode );
						}
					}
				}
			}
			;

const_list : const_list COMMA ID ASSIGN_OP literal_const
			{				
				addConstParam( $1, createConstParam( $5, $3 ) );
				$$ = $1;
			}
		   | ID ASSIGN_OP literal_const
			{
				$$ = createConstParam( $3, $1 );
				$$->flag = 1;
				
				/*
				struct SymNode *node;
				node = lookupSymbol( symbolTable, $1, scope, __FALSE);
				
				if(node->scope == 0){
					if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
						fprintf(output, "\tputstatic %s/%s I\n", fileName, $1);
					else
						fprintf(output, "\tputstatic %s/%s F\n", fileName, $1);
					}
				else{
					if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
						fprintf(output, "\tistore %d\n", node->order);
					else
						fprintf(output, "\tfstore %d\n", node->order);
				}*/
			}
		   ;

array_decl : ID dim 
			{
				$$ = createParam( createIdList( $1 ), $2 );
			}
		   ;

dim : dim ML_BRACE INT_CONST MR_BRACE
		{
			if( $3 == 0 ){
				fprintf( stdout, "########## Error at Line#%d: array size error!! ##########\n", linenum );
				semError = __TRUE;
			}
			else
				increaseArrayDim( $1, 0, $3 );			
		}
	| ML_BRACE INT_CONST MR_BRACE	
		{
			if( $2 == 0 ){
				fprintf( stdout, "########## Error at Line#%d: array size error!! ##########\n", linenum );
				semError = __TRUE;
			}			
			else{		
				$$ = createPType( VOID_t ); 			
				increaseArrayDim( $$, 0, $2 );
			}		
		}
	;
	
compound_statement : {scope++;}L_BRACE var_const_stmt_list R_BRACE
					{ 
						// print contents of current scope
						if( Opt_Symbol == 1 )
							printSymTable( symbolTable, scope );
							
						deleteScope( symbolTable, scope );	// leave this scope, delete...
						scope--; 
					}
				   ;

var_const_stmt_list : var_const_stmt_list statement	
				    | var_const_stmt_list var_decl
					| var_const_stmt_list const_decl
				    |
				    ;

statement : compound_statement
		  | simple_statement
		  | conditional_statement
		  | while_statement
		  | for_statement
		  | function_invoke_statement
		  | jump_statement
		  ;		

simple_statement : variable_reference ASSIGN_OP logical_expression SEMICOLON
					{
						// check if LHS exists
						__BOOLEAN flagLHS = verifyExistence( symbolTable, $1, scope, __TRUE );
						// id RHS is not dereferenced, check and deference
						__BOOLEAN flagRHS = __TRUE;
						if( $3->isDeref == __FALSE ) {
							flagRHS = verifyExistence( symbolTable, $3, scope, __FALSE );
						}
						// if both LHS and RHS are exists, verify their type
						if( flagLHS==__TRUE && flagRHS==__TRUE )
							verifyAssignmentTypeMatch( $1, $3 );
							
						struct SymNode *node;
						node = lookupSymbol( symbolTable, $1->varRef->id, scope, __FALSE);
						
						if(node->scope == 0){
							if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
								fprintf(output, "\tputstatic %s/%s I\n", fileName, $1->varRef->id);
							else
								fprintf(output, "\tputstatic %s/%s F\n", fileName, $1->varRef->id);
						}
						else{
							if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
								fprintf(output, "\tistore %d\n", node->order);
							else
								fprintf(output, "\tfstore %d\n", node->order);
						}
					}
				 | PRINT
					{
						fprintf(output, "\tgetstatic java/lang/System/out Ljava/io/PrintStream;\n");
					}
					logical_expression SEMICOLON 
					{
						verifyScalarExpr( $3, "print" ); 
						if(GetType($3->pType) == 'C')
							fprintf(output, "\tinvokevirtual java/io/PrintStream/print(Ljava/lang/String;)V\n");
						else if(GetType($3->pType) == 'U'){
							//printf("%c\n", GetType($3->pType));
							fprintf(output, "\tinvokevirtual java/io/PrintStream/print(%c)V\n", GetType($3->pType));
						}
						else{
							//printf("%c\n", GetType($3->pType));
							fprintf(output, "\tinvokevirtual java/io/PrintStream/print(%c)V\n", GetType($3->pType));
						}
							
					}
				 | READ variable_reference SEMICOLON 
					{ 
						if( verifyExistence( symbolTable, $2, scope, __TRUE ) == __TRUE )						
							verifyScalarExpr( $2, "read" ); 
						
						struct SymNode *node;
						node = lookupSymbol( symbolTable, $2->varRef->id, scope, __FALSE);
						
						fprintf(output, "\tgetstatic %s/_sc Ljava/util/Scanner;\n", fileName);
						if(GetType($2->pType) == 'I'){
							fprintf(output, "\tinvokevirtual java/util/Scanner/nextInt()I\n");
							fprintf(output, "\tistore %d\n", node->order);
						}
						else{
							fprintf(output, "\tinvokevirtual java/util/Scanner/nextFloat()F\n");
							fprintf(output, "\tfstore %d\n", node->order);
						}
					}
				 ;
				 		 
conditional_statement : IF L_PAREN conditional_if R_PAREN compound_statement
						{
							fprintf(output, "L_else_%d:\n", Label++);
						}
					  | IF L_PAREN conditional_if R_PAREN compound_statement
						{
							fprintf(output, "\tgoto L_exit_%d\n", Label);
							fprintf(output, "L_else_%d:\n", Label);
						}
						ELSE compound_statement
						{
							fprintf(output, "L_exit_%d:\n", Label);
						}
					  ;
conditional_if : logical_expression 
				{	
					Loop++;
					Label = Loop;
					//fprintf(output, "\tgoto L%d\n", Label);
					fprintf(output, "\tifeq L_else_%d\n", Label);
					verifyBooleanExpr( $1, "if" ); 
				};					  

			
while_statement : WHILE L_PAREN 
				{
					Label = Loop;
					Loop++;
					fprintf(output, "L_begin_%d:\n", Label);
					Label++;
				}
				  logical_expression 
				{ 
					verifyBooleanExpr( $4, "while" );
				}
					R_PAREN 
				{ 
					inloop++; 
					fprintf(output, "\tifeq L_exit_%d\n", Label);
				}
					compound_statement 
				{ 
					fprintf(output, "\tgoto L_begin_%d\n", Label);
					fprintf(output, "L_exit_%d:\n", Label);
					inloop--;
				}
				| { inloop++; } DO compound_statement WHILE L_PAREN logical_expression R_PAREN SEMICOLON  
					{ 
						 verifyBooleanExpr( $6, "while" );
						 inloop--; 
						
					}
				;

				
for_statement : FOR L_PAREN initial_expression SEMICOLON
				{		
					Label = Loop;
					Loop++;
					fprintf(output, "L_for_begin_%d:\n", Label);
					Label++;		
				}
				control_expression SEMICOLON 
				{
					fprintf(output, "\tifeq L_for_exit_%d\n", Label);
					fprintf(output, "\tgoto L_for_true_%d\n", Label);
					fprintf(output, "L_for_inc_%d:\n", Label);
				}
				increment_expression R_PAREN  
				{ 
					fprintf(output, "\tgoto L_for_begin_%d\n", Label);
					fprintf(output, "L_for_true_%d:\n", Label);
					
					inloop++;
				}
				compound_statement  
				{
					fprintf(output, "\tgoto L_for_inc_%d\n", Label);
					fprintf(output, "L_for_exit_%d:\n", Label);
					inloop--;
				}
			  ;

initial_expression : initial_expression COMMA statement_for		
				   | initial_expression COMMA logical_expression
				   | logical_expression	
				   | statement_for
				   |
				   ;

control_expression : control_expression COMMA statement_for
				   {
						fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
						semError = __TRUE;	
				   }
				   | control_expression COMMA logical_expression
				   {
						if( $3->pType->type != BOOLEAN_t ){
							fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
							semError = __TRUE;	
						}
				   }
				   | logical_expression 
					{ 
						if( $1->pType->type != BOOLEAN_t ){
							fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
							semError = __TRUE;	
						}
					}
				   | statement_for
				   {
						fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
						semError = __TRUE;	
				   }
				   |
				   ;

increment_expression : increment_expression COMMA statement_for
					 | increment_expression COMMA logical_expression
					 | logical_expression
					 | statement_for
					 |
					 ;

statement_for 	: variable_reference ASSIGN_OP logical_expression
					{
						// check if LHS exists
						__BOOLEAN flagLHS = verifyExistence( symbolTable, $1, scope, __TRUE );
						// id RHS is not dereferenced, check and deference
						__BOOLEAN flagRHS = __TRUE;
						if( $3->isDeref == __FALSE ) {
							flagRHS = verifyExistence( symbolTable, $3, scope, __FALSE );
						}
						// if both LHS and RHS are exists, verify their type
						if( flagLHS==__TRUE && flagRHS==__TRUE )
							verifyAssignmentTypeMatch( $1, $3 );
						
						struct SymNode *node;
						node = lookupSymbol( symbolTable, $1->varRef->id, scope, __FALSE);
						
						if(node->scope == 0){
							if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
								fprintf(output, "\tputstatic %s/%s I\n", fileName, $1->varRef->id);
							else
								fprintf(output, "\tputstatic %s/%s F\n", fileName, $1->varRef->id);
						}
						else{
							if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
								fprintf(output, "\tistore %d\n", node->order);
							else
								fprintf(output, "\tfstore %d\n", node->order);
						}
					}
					;
					 
					 
function_invoke_statement : ID L_PAREN logical_expression_list R_PAREN SEMICOLON
							{
								//printf("yo\n");
								fprintf(output, "\tinvokestatic %s/%s(", fileName, $1);
								struct expr_sem *ptr;
								//printf("a");
								ptr = $3;
								fprintf(output, "%c", GetType(ptr->pType));
								for(ptr = $3->next; ptr != 0; ptr = (ptr->next)){
									fprintf(output, "%c", GetType(ptr->pType));
								}
								struct SymNode *node;
								node = lookupSymbol(symbolTable, $1, scope, __FALSE);
								fprintf(output, ")%c\n", GetType(node->type));
							
								verifyFuncInvoke( $1, $3, symbolTable, scope );	
							}
						  | ID L_PAREN R_PAREN SEMICOLON
							{
								struct SymNode *node;
								node = lookupSymbol(symbolTable, $1, scope, __FALSE);		
								fprintf(output, "\tinvokestatic %s/%s()%c\n", fileName, $1, GetType(node->type));
								verifyFuncInvoke( $1, 0, symbolTable, scope );
							}
						  ;

jump_statement : CONTINUE SEMICOLON
				{
					if( inloop <= 0){
						fprintf( stdout, "########## Error at Line#%d: continue can't appear outside of loop ##########\n", linenum ); semError = __TRUE;
					}
				}
			   | BREAK SEMICOLON 
				{
					if( inloop <= 0){
						fprintf( stdout, "########## Error at Line#%d: break can't appear outside of loop ##########\n", linenum ); semError = __TRUE;
					}
				}
			   | RETURN logical_expression SEMICOLON
				{
					if(GetType(funcReturn) == 'V')
						fprintf(output, "\treturn\n");
					else if(GetType(funcReturn) == 'I' || GetType(funcReturn) == 'Z')
						fprintf(output, "\tireturn\n");
					else if(GetType(funcReturn) == 'F')
						fprintf(output, "\tfreturn\n");
						
					verifyReturnStatement( $2, funcReturn );
				}
			   ;

variable_reference : ID
					{	
						$$ = createExprSem( $1 );		
					}
				   | variable_reference dimension
					{	
						increaseDim( $1, $2 );
						$$ = $1;
					}
				   ;

dimension : ML_BRACE arithmetic_expression MR_BRACE
			{
				$$ = verifyArrayIndex( $2 );
			}
		  ;
		  
logical_expression : logical_expression OR_OP logical_term
					{
						verifyAndOrOp( $1, OR_t, $3 );
						$$ = $1;
						fprintf(output, "\tior\n");
					}
				   | logical_term { $$ = $1; }
				   ;

logical_term : logical_term AND_OP logical_factor
				{
					verifyAndOrOp( $1, AND_t, $3 );
					$$ = $1;
					fprintf(output, "\tiand\n");
				}
			 | logical_factor { $$ = $1; }
			 ;

logical_factor : NOT_OP logical_factor
				{
					verifyUnaryNOT( $2 );
					$$ = $2;
					fprintf(output, "\tixor\n");
				}
			   | relation_expression { $$ = $1; }
			   ;

relation_expression : arithmetic_expression relation_operator arithmetic_expression
					{
						verifyRelOp( $1, $2, $3 );
						$$ = $1;
						
						if(GetType($1->pType) == 'F' && GetType($3->pType) == 'F')
							fprintf(output, "\tfcmpl\n");
						else if(GetType($1->pType) == 'F' && GetType($3->pType) == 'I'){
							fprintf(output, "\tswap\n");
							fprintf(output, "\ti2f\n");
							fprintf(output, "\tfcmpl\n");
						}
						else if(GetType($1->pType) == 'I' && GetType($3->pType) == 'F'){
							fprintf(output, "\ti2f\n");
							fprintf(output, "\tfcmpl\n");
						}
						else if(GetType($1->pType) == 'F' || GetType($3->pType) == 'F')
							fprintf(output, "\tfcmpl\n");
						else{
							//printf("%c   %c\n", GetType($1->pType), GetType($3->pType));
							fprintf(output, "\tisub\n");
						}
							
						
						if($2 == LT_t)
							fprintf(output, "\tiflt L_true_%d\n", Label);
						else if($2 == LE_t)
							fprintf(output, "\tifle L_true_%d\n", Label);
						else if($2 == EQ_t)
							fprintf(output, "\tifeq L_true_%d\n", Label);
						else if($2 == GE_t)
							fprintf(output, "\tifge L_true_%d\n", Label);
						else if($2 == GT_t)
							fprintf(output, "\tifgt L_true_%d\n", Label);
						else if($2 == NE_t)
							fprintf(output, "\tifne L_true_%d\n", Label);
						
						fprintf(output, "\ticonst_0\n");
						fprintf(output, "\tgoto L_false_%d\n", Label);
						fprintf(output, "L_true_%d:\n", Label);
						fprintf(output, "\ticonst_1\n");
						fprintf(output, "L_false_%d:\n", Label--);
					}
					| arithmetic_expression { $$ = $1; }
					;

relation_operator : LT_OP { $$ = LT_t; }
				  | LE_OP { $$ = LE_t; }
				  | EQ_OP { $$ = EQ_t; }
				  | GE_OP { $$ = GE_t; }
				  | GT_OP { $$ = GT_t; }
				  | NE_OP { $$ = NE_t; }
				  ;

arithmetic_expression : arithmetic_expression add_op term
			{
				verifyArithmeticOp( $1, $2, $3 );
				$$ = $1;
				if(GetType($3->pType) == 'I' && GetType($1->pType) == 'F'){
					fprintf(output, "\tistore %d\n", stack);
					fprintf(output, "\tiload %d\n", stack);
					fprintf(output, "\ti2f\n");
				}
				else if(GetType($3->pType) == 'I' && GetType($1->pType) == 'I'){
					fprintf(output, "\tistore %d\n", stack);
					fprintf(output, "\tiload %d\n", stack);
				}
				else if(GetType($3->pType) == 'F' && GetType($1->pType) == 'I'){
					fprintf(output, "\tfstore %d\n", stack);
					fprintf(output, "\tfload %d\n", stack);
					fprintf(output, "\ti2f\n");
				}
				else{
					fprintf(output, "\tfstore %d\n", stack);
					fprintf(output, "\tfload %d\n", stack);
				}
				
					
				if(GetType($1->pType) == 'I' && GetType($3->pType) == 'I' && $2 == ADD_t){
					fprintf(output, "\tiadd\n");
				}
				else if(GetType($1->pType) == 'I' && GetType($3->pType) == 'I' && $2 == SUB_t)
					fprintf(output, "\tisub\n");
				else if($2 == ADD_t)
					fprintf(output, "\tfadd\n");
				else if($2 == SUB_t)
					fprintf(output, "\tfsub\n");	
			}
		   | term { $$ = $1; }
		   ;

add_op	: ADD_OP { $$ = ADD_t; }
		| SUB_OP { $$ = SUB_t; }
		;
		   
term : term mul_op factor
		{
			if( $2 == MOD_t ) {
				verifyModOp( $1, $3 );
			}
			else {
				verifyArithmeticOp( $1, $2, $3 );
			}
			$$ = $1;
			
			if(GetType($3->pType) == 'I' && GetType($1->pType) == 'F'){
					fprintf(output, "\tistore %d\n", stack);
					fprintf(output, "\tiload %d\n", stack);
					fprintf(output, "\ti2f\n");
				}
				else if(GetType($3->pType) == 'I' && GetType($1->pType) == 'I'){
					fprintf(output, "\tistore %d\n", stack);
					fprintf(output, "\tiload %d\n", stack);
				}
				else if(GetType($3->pType) == 'F' && GetType($1->pType) == 'I'){
					fprintf(output, "\tfstore %d\n", stack);
					fprintf(output, "\tfload %d\n", stack);
					fprintf(output, "\ti2f\n");
				}
				else{
					fprintf(output, "\tfstore %d\n", stack);
					fprintf(output, "\tfload %d\n", stack);
				}
			
			if(GetType($1->pType) == 'I' && GetType($3->pType) == 'I' && $2 == MUL_t)
				fprintf(output, "\timul\n");
			else if(GetType($1->pType) == 'I' && GetType($3->pType) == 'I' && $2 == DIV_t)
				fprintf(output, "\tidiv\n");
			else if(GetType($1->pType) == 'I' && GetType($3->pType) == 'I' && $2 == MOD_t)
				fprintf(output, "\tirem\n");
			else if($2 == MUL_t)
				fprintf(output, "\tfmul\n");
			else if($2 == DIV_t)
				fprintf(output, "\tfdiv\n");
			else if($2 == MOD_t)
				fprintf(output, "\tfrem\n");	
		}
     | factor 
	 { $$ = $1;
		if($$->beginningOp == SUB_t){
			if(GetType($1->pType) == 'I')
				fprintf(output, "\tineg\n");
			else
				fprintf(output, "\tfneg\n");
		}	
	}
	 ;

mul_op 	: MUL_OP { $$ = MUL_t; }
		| DIV_OP { $$ = DIV_t; }
		| MOD_OP { $$ = MOD_t; }
		;
		
factor : variable_reference
		{
			struct SymNode *node;
			//printf("%s\n", $1->varRef->id);
			node = lookupSymbol( symbolTable, $1->varRef->id, scope, __FALSE);
			verifyExistence( symbolTable, $1, scope, __FALSE );
			$$ = $1;
			$$->beginningOp = NONE_t;		
			//$$->isconst = 0;
			//printf("%s  %d   %d\n", $1->varRef->id, node->scope, node->order);
			if(node->flag == 0){
				if(node->scope == 0)
					fprintf(output, "\tgetstatic %s/%s %c\n", fileName, $1->varRef->id, GetType(node->type));
				else{
					if(GetType(node->type) == 'I' || GetType(node->type) == 'Z')
						fprintf(output, "\tiload %d\n", node->order);
					else
						fprintf(output, "\tfload %d\n", node->order);
				}
			}
			else{
				if(GetType(node->type) == 'I')
					fprintf(output, "\tsipush %d\n", node->attribute->constVal->value);
				else if(GetType(node->type) == 'F')
					fprintf(output, "\tldc %d\n", node->attribute->constVal->value);
				else if(GetType(node->type) == 'Z')
					fprintf(output, "\ticonst_%d\n", node->attribute->constVal->value);
				else if(GetType(node->type) == 'C'){
					fprintf(output, "\tldc \"");
					int i = 0;
					while(node->attribute->constVal->value.stringVal[i] != '\0'){
						if(node->attribute->constVal->value.stringVal[i] == '\n')
							fprintf(output, "\\n");
						else if(node->attribute->constVal->value.stringVal[i] == '\t')
							fprintf(output, "\\t");
						else
							fprintf(output, "%c", node->attribute->constVal->value.stringVal[i]);
							
						i++;
					}
					fprintf(output, "\"\n");
				}
			}
			
		}
	   | SUB_OP variable_reference
		{
			if( verifyExistence( symbolTable, $2, scope, __FALSE ) == __TRUE )
			verifyUnaryMinus( $2 );
			$$ = $2;
			$$->beginningOp = SUB_t;
		}		
	   | L_PAREN logical_expression R_PAREN
		{
			$2->beginningOp = NONE_t;
			$$ = $2; 
		}
	   | SUB_OP L_PAREN logical_expression R_PAREN
		{
			verifyUnaryMinus( $3 );
			$$ = $3;
			$$->beginningOp = SUB_t;
		}
	   | ID L_PAREN logical_expression_list R_PAREN
		{
			//printf("yo\n");
			fprintf(output, "\tinvokestatic %s/%s(", fileName, $1);
			struct expr_sem *ptr;
			//printf("a");
			ptr = $3;
			fprintf(output, "%c", GetType(ptr->pType));
			for(ptr = $3->next; ptr != 0; ptr = (ptr->next)){
				fprintf(output, "%c", GetType(ptr->pType));
			}
			struct SymNode *node;
			node = lookupSymbol(symbolTable, $1, scope, __FALSE);
			fprintf(output, ")%c\n", GetType(node->type));
			
			$$ = verifyFuncInvoke( $1, $3, symbolTable, scope );
			$$->beginningOp = NONE_t;
		}
	   | SUB_OP ID L_PAREN logical_expression_list R_PAREN
	    {
			$$ = verifyFuncInvoke( $2, $4, symbolTable, scope );
			$$->beginningOp = SUB_t;
		}
	   | ID L_PAREN R_PAREN
		{
			$$ = verifyFuncInvoke( $1, 0, symbolTable, scope );
			$$->beginningOp = NONE_t;
		}
	   | SUB_OP ID L_PAREN R_PAREN
		{	
			$$ = verifyFuncInvoke( $2, 0, symbolTable, scope );
			$$->beginningOp = SUB_OP;
		}
	   | literal_const
	    {
			  $$ = (struct expr_sem *)malloc(sizeof(struct expr_sem));
			  $$->isDeref = __TRUE;
			  $$->varRef = 0;
			  $$->pType = createPType( $1->category );
			  $$->next = 0;
			  //$$->isconst = 1;
			  if( $1->hasMinus == __TRUE ) {
			  	$$->beginningOp = SUB_t;
			  }
			  else {
				$$->beginningOp = NONE_t;
			  }
			  
			  char type;
			  type = GetType($$->pType);
			  if(type == 'C'){
				fprintf(output, "\tldc \"");
				int i = 0;
				while($1->value.stringVal[i] != '\0'){
					if($1->value.stringVal[i] != '\n')
						fprintf(output, "%c", $1->value.stringVal[i]);
					else
						fprintf(output, "\\n");
					i++;
				}
				fprintf(output, "\"\n");
			  }
			  else if(type == 'I')
				fprintf(output, "\tldc %d\n", $1->value.integerVal);
			  else if(type == 'Z')
				fprintf(output, "\ticonst_%d\n", $1->value.booleanVal);
			  else if(type == 'F')
				fprintf(output, "\tldc %f\n", $1->value.floatVal);
		}
	   ;

logical_expression_list : logical_expression_list COMMA logical_expression
						{
			  				struct expr_sem *exprPtr;
			  				for( exprPtr=$1 ; (exprPtr->next)!=0 ; exprPtr=(exprPtr->next) );
			  				exprPtr->next = $3;
			  				$$ = $1;
						}
						| logical_expression { $$ = $1; }
						;

		  


scalar_type : INT { $$ = createPType( INTEGER_t ); }
			| DOUBLE { $$ = createPType( DOUBLE_t ); }
			| STRING { $$ = createPType( STRING_t ); }
			| BOOL { $$ = createPType( BOOLEAN_t ); }
			| FLOAT { $$ = createPType( FLOAT_t ); }
			;
 
literal_const : INT_CONST
				{
					int tmp = $1;
					$$ = createConstAttr( INTEGER_t, &tmp );
				}
			  | SUB_OP INT_CONST
				{
					int tmp = -$2;
					$$ = createConstAttr( INTEGER_t, &tmp );
				}
			  | FLOAT_CONST
				{
					float tmp = $1;
					$$ = createConstAttr( FLOAT_t, &tmp );
				}
			  | SUB_OP FLOAT_CONST
			    {
					float tmp = -$2;
					$$ = createConstAttr( FLOAT_t, &tmp );
				}
			  | SCIENTIFIC
				{
					double tmp = $1;
					$$ = createConstAttr( DOUBLE_t, &tmp );
				}
			  | SUB_OP SCIENTIFIC
				{
					double tmp = -$2;
					$$ = createConstAttr( DOUBLE_t, &tmp );
				}
			  | STR_CONST
				{
					$$ = createConstAttr( STRING_t, $1 );
				}
			  | TRUE
				{
					SEMTYPE tmp = __TRUE;
					$$ = createConstAttr( BOOLEAN_t, &tmp );
				}
			  | FALSE
				{
					SEMTYPE tmp = __FALSE;
					$$ = createConstAttr( BOOLEAN_t, &tmp );
				}
			  ;
%%

int yyerror( char *msg )
{
    fprintf( stderr, "\n|--------------------------------------------------------------------------\n" );
	fprintf( stderr, "| Error found in Line #%d: %s\n", linenum, buf );
	fprintf( stderr, "|\n" );
	fprintf( stderr, "| Unmatched token: %s\n", yytext );
	fprintf( stderr, "|--------------------------------------------------------------------------\n" );
	exit(-1);
}


