" Vim syntax file
" Language: Silver

" exit if syntax already loaded
if exists("b:current_syntax")
	finish
endif

" keywords and regexes copied from gedit and google-code-prettyify

syn keyword svlangExternals grammar import imports exports build hiding as only option

syn keyword svlangDeclarations parser attribute annotation function local closed nonterminal type occurs on production terminal marking foreign layout disambiguate action global productions lexer class default

syn keyword svlangPrimitiveTypes IO Boolean Decorated Float Function Integer Production String

syn keyword svlangStorageClass abstract aspect concrete inherited synthesized autocopy ignore

syn keyword svlangScopeDeclarations association precedence operator dominates submits classes

syn keyword svlangFlowOther forwarding forwards to return pluck

syn keyword svlangFlow case of let in end decorate with prefix else forward if new then

syn keyword svlangFunction print toString toInt toFloat length reference substring indexOf error cast left right

"syn keyword svlangIde temp_imp_ide_dcl temp_imp_ide_font font color italic bold

"syn keyword svlangIdeInner contained builder postbuilder exporter folder property string required string wizard new file stub generator product name version option resource

syn keyword svlangBoolean false true

syn keyword svlangTodo contained TODO FIXME XXX

syn region svlangBlock start=/\v\{/ end=/\v\}/		transparent fold
syn region svlangDocComment start=/\v\{--/ end=/\v-\}/	contains=svlangTodo,svlangBlockComment,svlangDocComment,svlangDocTags,svlangDocSeeTag fold
syn region svlangBlockComment start=/\v\{-[^-]/ end=/\v-\}/	contains=svlangTodo,svlangBlockComment,svlangDocComment fold
syn match svlangComment /\v--.*/ 			contains=svlangTodo
syn match svlangRegex /\v\/((\\\/)|[^/])*\//
syn region svlangString start=/\v"/ skip=/\v\\"/ end=/\v"|$/	contains=svlangEscapedChar
syn match svlangCharacter /\v\'\\?.\'/			contains=svlangEscapedChar
syn match svlangEscapedChar display contained /\v\\([\\"\'nrbtf]|\d{1,3}|u\d{1,4})/
syn match svlangNumeric /\v<(0[xX])?\d+[lL]?>/
syn match svlangFloat /\v<(\d+[eE][-+]?\d+)|(\d*\.\d\+([eE][-+]?\d+)?[fFdD]?)|(\d\+[fFdD])>/
"syn match svlangOperator /\v[+-]|\=|\:|\*|\//

" copied from /usr/share/vim/vim73/syntax/java.vim
syn region svlangDocTags	 contained start="{@\(link\|linkplain\|inherit[Dd]oc\|doc[rR]oot\|value\)" end="}"
syn match  svlangDocTags	 contained "@\(param\|exception\|throws\|since\)\s\+\S\+" contains=svlangDocParam
syn match  svlangDocParam	 contained "\s\S\+"
syn match  svlangDocTags	 contained "@\(version\|author\|return\|deprecated\|serial\|serialField\|serialData\)\>"
syn region svlangDocSeeTag	 contained matchgroup=svlangDocTags start="@see\s\+" matchgroup=NONE end="\_."re=e-1 contains=svlangDocSeeTagParam
syn match  svlangDocSeeTagParam  contained @"\_[^"]\+"\|<a\s\+\_.\{-}</a>\|\(\k\|\.\)*\(#\k\+\((\_[^)]\+)\)\=\)\=@ extend


syntax sync fromstart

hi def link svlangExternals		Include
hi def link svlangDeclarations		Keyword
hi def link svlangPrimitiveTypes	Type
hi def link svlangStorageClass	 	StorageClass
hi def link svlangScopeDeclarations	Keyword
hi def link svlangFlowOther		Statement
hi def link svlangFlow		 	Statement
"hi def link svlangIde			Type
"hi def link svlangIdeInner		Keyword
hi def link svlangBoolean		Boolean
hi def link svlangComment		Comment
hi def link svlangDocComment		Comment
hi def link svlangBlockComment		Comment
hi def link svlangRegex		 	String
hi def link svlangString		String
hi def link svlangCharacter		Character
hi def link svlangEscapedChar		SpecialChar
hi def link svlangNumeric		Number
hi def link svlangFloat		 	Float
hi def link svlangTodo		 	Todo
hi def link svlangFunction	 	Function
"hi def link svlangOperator	 	Operator
hi def link svlangDocTags		Special
hi def link svlangDocParam		Function
hi def link svlangDocSeeTagParam	Function

set autoindent
set expandtab
set shiftwidth=2
set softtabstop=2

