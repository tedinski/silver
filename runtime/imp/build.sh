#!/bin/bash

# On CS machines, load the module 'java/maven'

set -e

### Sanity checks
if [ ! -d ../../runtime ]; then
  echo "In wrong directory?  Run from silver/runtime/imp as ./build.sh"
  exit 1
fi

cd main

### clean up generated code that's stale
if [ -d src/core ]; then
  rm -rf src/core src/ide src/silver
fi

### regenerate fresh code:

# We need to build this with the knowledge of what's generated by the grammars
# core and ide. So use silver to generate the corresponding java files here.
java -jar ../../../jars/silver.composed.Default.jar -G . ide
rm build.xml

### build
mvn clean package

#cp target/edu.umn.cs.melt.ide*.jar ../../../jars/IDEPluginRuntime.jar

### Okay, we cheated to get core and ide in. Now strip them.
mkdir temp
cd temp
jar xf ../target/edu.umn.cs.melt.ide*.jar
rm -r ide core silver
jar cmf META-INF/MANIFEST.MF ../IDEPluginRuntime.jar *
cd ..
rm -r temp
mv IDEPluginRuntime.jar ../../../jars/

# Avoid cleaning up generated code too eagerly, let the next run do it.
#rm -r src/core src/ide

# unnecessary, but for symmetry, leave 'main'
cd ..

