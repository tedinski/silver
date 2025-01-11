-- Test to ensure that no two annotations occuring on the same nonterminal can have the same shortname

imports silver_features:anno_short_names:a as a;
imports silver_features:anno_short_names:b as b;
imports silver_features:anno_short_names:c as c;

wrongCode "already occurs on" {
    nonterminal Thing1 ;
    annotation a:foo occurs on Thing1;
    annotation b:foo occurs on Thing1;
}

wrongCode "already occurs on" {
    nonterminal Thing2 with a:foo;
    annotation b:foo occurs on Thing2;
}

wrongCode "already occurs on" {
    nonterminal Thing3 with a:foo, b:foo;
}

-- no error here
nonterminal Thing4 with a:foo, c:foo;
nonterminal Thing5 with a:baz, b:baz;