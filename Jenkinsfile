#!groovy

library "github.com/melt-umn/jenkins-lib"

melt.setProperties(overrideJars: true)

melt.trynode('silver') {
  def WS = pwd()
  def newenv = silver.getSilverEnv(WS)

  stage("Build") {

    melt.clearGenerated()

    checkout scm

    // Bootstrap logic to obtain jars
    if (params.OVERRIDE_JARS != 'no') {
      def source = params.OVERRIDE_JARS
      if (source == 'develop') {
        source = "${silver.SILVER_WORKSPACE}/jars"
      }
      String branchJob = "/melt-umn/silver/${hudson.Util.rawEncode(source)}"
      if(melt.doesJobExist(branchJob)) {
        // Obtain jars from specified branch
        melt.annotate("Jars overidden from branch.")
        copyArtifacts(projectName: branchJob, selector: lastCompleted())
      } else {
        // Obtain jars from specified location
        melt.annotate("Jars overridden from path.")
        sh "mkdir -p jars"
        sh "cp ${source}/* jars/"
      }
    } else {
      def foundJars = false
      if (env.BRANCH_NAME == 'develop') {
        // For 'develop', detect pull request merges, and grab jars from the merged branch
        String branch = getMergedBranch()
        if (branch) {
          echo "Trying to get jars from merged branch ${branch}"
          String branchJob = "/melt-umn/silver/${hudson.Util.rawEncode(branch)}"
          if(melt.doesJobExist(branchJob)) {
            try {
              copyArtifacts(projectName: branchJob, selector: lastSuccessful())
              melt.annotate("Jars from merged branch.")
              foundJars = true
            } catch (hudson.AbortException exc1) {
              // That's okay. We prefer this approach to using 'optional: true' because it
              // lets us know whether it happened or not. The annotation only gets set when it does.
            }
          }
        }
      } else if (env.BRANCH_NAME != 'master') {
        // For branches, try to obtain jars from previous builds.
        try {
          // If the last build has artifacts, use those.
          copyArtifacts(projectName: env.JOB_NAME, selector: lastCompleted())
          melt.annotate("Jars from branch (prev).")
          foundJars = true
        } catch (hudson.AbortException exc2) {
          try {
            // If there is a last successful build, use those.
            copyArtifacts(projectName: env.JOB_NAME, selector: lastSuccessful())
            melt.annotate("Jars from branch (successful).")
            foundJars = true
          } catch (hudson.AbortException exc3) {
            // That's okay. We tried. We'll stick with fetch-jars
          }
        }
      }
      if (!foundJars) {
        // Fall back to using fetch-jars
        sh "./fetch-jars"
      }
    }
    // If requested, go download the latest Copper jars and use them instead of the archived/provided ones
    if (params.FETCH_COPPER_JARS == 'yes') {
      echo "Fetching lastest Copper jars"
      melt.annotate("Fetched Copper jars.")
      sh "./fetch-jars --copper"
    }
    // Build
    sh "./deep-rebuild"
    // Clean (but leave generated files)
    sh "./deep-clean -delete"
    // Generate docs
    sh "./make-docs"
    // Upon succeeding at initial build, archive for future builds
    archiveArtifacts(artifacts: "jars/*.jar", fingerprint: true)
    melt.archiveCommitArtifacts("jars/*.jar")
  }

  stage("Language server") {
    sh "./make-vscode-extension"
    archiveArtifacts(artifacts: "support/vs-code/silverlsp/*.vsix", fingerprint: true)
    melt.archiveCommitArtifacts("support/vs-code/silverlsp/*.vsix")
  }

  stage("Package") {
    sh "rm -rf silver-latest* || true" // Robustness to past failures
    sh "./make-dist latest"
  }

  stage("Modular Analyses") {
    sh "./check-compile --clean --mwda"
  }

  // Avoid deadlock condition from all executor slots being filled with builds
  // that are waiting for downstream builds to finish.
  waitUntil { melt.isExecutorAvailable() }

  stage("Test") {
    // These test cases and tutorials are run as seperate tasks to allow for parallelism
    def tests = ["silver_features", "copper_features", "patt", "flow", "stdlib", "performance", "csterrors", "silver_construction", "origintracking", "implicit_monads"]
    def tuts = ["simple/with_all", "simple/with_do_while", "simple/with_repeat_until", "simple/with_implication", "simple/host", "simple/arb_host", "simple/arb_with_all", "dc", "lambda", "turing", "hello", "stlc"]

    def tasks = [:]
    tasks << tests.collectEntries { t -> [(t): task_test(t, WS)] }
    tasks << tuts.collectEntries { t -> [(t): task_tutorial(t, WS)] }

    // Build test driver
    withEnv (newenv) {
      dir ("${WS}/test") {
        sh "silver --clean -I ${WS}/grammars silver:testing:bin"
      }
    }

    // Unpack tarball (into ./silver-latest/) (for tutorial testing)
    sh "tar zxf silver-latest.tar.gz"
    // Run tests
    parallel tasks
    // Clean
    sh "rm -rf silver-latest"
  }

  // Avoid deadlock condition from all executor slots being filled with builds
  // that are waiting for downstream builds to finish.
  waitUntil { melt.isExecutorAvailable() }

  stage("Integration") {
    // Projects with 'develop' as main branch, we'll try to build specific branch names if they exist
    def github_projects = ["/melt-umn/ableC", "/melt-umn/Oberon0", "/melt-umn/meta-ocaml-lite",
                           "/melt-umn/lambda-calculus", "/melt-umn/rewriting-regex-matching", "/melt-umn/rewriting-optimization-demo",
                           "/melt-umn/caml-light", "/melt-umn/tree-sharing-demo"]
    // These are not currently maintened: "/internal/ring"
    // Specific other jobs to build
    def specific_jobs = ["/internal/matlab/master"]
    // AbleP is now downstream from Silver-AbleC, so we don't need to build it here: "/melt-umn/ableP/master"
    // These are not currently maintened: "/internal/simple/master"

    def tasks = [:]
    tasks << github_projects.collectEntries { t ->
      [(t): { melt.buildProject(t, [SILVER_BASE: WS]) }]
    }
    tasks << specific_jobs.collectEntries { t ->
      [(t): { melt.buildJob(t, [SILVER_BASE: WS]) }]
    }

    // Do downstream integration testing
    parallel tasks
  }

  if (env.BRANCH_NAME == 'develop') {
    stage("Deploy") {
      sh "rsync -a --exclude .git --exclude generated --exclude silver-latest.tar.gz --delete --delete-excluded ./ ${silver.SILVER_WORKSPACE}/"
      // -a is archive mode: rlptgoD (recurse, links, perms, time, group, owner, devices)
      // --delete  Remove files from destination not in src
      // --delete-excluded  Remove files from dest that we're excluding
      // NOTE: we exclude generated, which means there's no generated dir in the custom
      // location, which means if you don't set it, things should blow up.

      sh "rsync -a --delete generated/doc/ ${silver.SILVER_WORKSPACE}/../custom-silver-doc/"

      sh "cp silver-latest.tar.gz ${melt.ARTIFACTS}/"
      sh "cp jars/*.jar ${melt.ARTIFACTS}/"
      sh "cp support/vs-code/silverlsp/silverlsp-latest.vsix ${melt.ARTIFACTS}/"

      build "/melt-umn/melt-website/master"
    }
  }

}

// If the last commit was a pull request merge, get the name of the merged branch
def getMergedBranch() {
  String commit_msg = sh(script: "git log --format=%B -n 1 HEAD", returnStdout: true)
  // Matcher cannot be serialized, but we can't mark this function @NonCPS because above we use 'sh'
  // So, YOLO, we probably won't get paused before we return!
  java.util.regex.Matcher merge_branch = commit_msg =~ /^Merge pull.*from melt-umn\/(.*)/
  if (merge_branch.find()) {
    return merge_branch.group(1)
  }
}

// Test in local workspace
def task_test(String testname, String WS) {
  def newenv = silver.getSilverEnv(WS)
  return {
    node {
      sh "touch ensure_workspace" // convince jenkins to create our workspace
      def GEN = pwd() // This node's workspace
      // Go back to our "parent" workspace, into the tests directory
      dir(WS + '/test/') {
        // HACK: edit the test specs to specify the generated directory
        sh "./set-generated-dir ${GEN} ${testname}"
        // Run the tests
        withEnv (newenv) {
          echo "Running test ${testname}"
          sh "java -jar silver.testing.bin.jar ${testname}"
        }
      }
      // Blow away these generated files in our private workspace
      deleteDir()
    }
  }
}
// Tutorial, in silver-latest
def task_tutorial(String tutorialpath, String WS) {
  return {
    node {
      sh "touch ensure_workspace" // convince jenkins to create our workspace
      def GEN = pwd() // This node's workspace
      echo "\nRemember that tutorials are built in 'silver-latest'.\nThis only includes files distributed with the tarball according to 'make-dist'.\n"
      dir(WS + '/silver-latest/tutorials/' + tutorialpath) {
        sh "./silver-compile --clean -G ${GEN}"
        sh "rm *.jar"
      }
      // Blow away these generated files in our private workspace
      deleteDir()
    }
  }
}

