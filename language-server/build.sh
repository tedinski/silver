#!/bin/bash

set -e

# For now, this expects you to have Copper installed locally;
# this can be done by running `mvn install` from wherever you have the copper repo checkedd out.

mvn install:install-file -Dfile=../jars/silver.core.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver-core -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
mvn install:install-file -Dfile=../jars/silver.util.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver-util -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
mvn install:install-file -Dfile=../jars/silver.langutil.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver-langutil -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
mvn install:install-file -Dfile=../jars/silver.rewrite.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver-rewrite -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
mvn install:install-file -Dfile=../jars/silver.regex.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver-regex -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
mvn install:install-file -Dfile=../jars/silver.compiler.composed.Default.jar -DgroupId=edu.umn.cs.melt -DartifactId=silver -Dversion=0.6.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true

(cd ../runtime/lsp4j && mvn install)

mvn package

cp launcher/target/launcher.jar ../jars/silver-langserver-launcher.jar
