package common;

import common.exceptions.SilverExit;
import java.io.*;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.jar.JarFile;
import java.util.jar.JarEntry;
import silver.core.NIOVal;
import silver.core.Pioval;
import silver.core.Pjust;
import silver.core.Pnothing;

/**
 * This class represents the `<code>IO</code>` type in Silver.
 *
 * <p>By convention we translate a Silver IO call of the form
 * `<code>IO ::= args IO</code>` to a method with the signature
 * `<code>IOToken f(args)</code>`. We return `this` or `this.wrap`
 * and the final `IO` argument is used to invoke the method.
 *
 * <p>`<code>iotoken.print(str)</code>` means the `IOToken` must be demanded
 * before the method can be invoked, which is the desired invariant.
 *
 * <p>Silver types are used in argument wherever possible, except for
 * primitives like `int`.
 *
 * @author tedinski
 */
public final class IOToken implements Typed {
  public static final IOToken singleton = new IOToken();

  private IOToken() {}

  /**
   * Function that return IOToken can return `this`.
   * Those that return `IOVal<>` can return `this.wrap(...)`.
   */
  public NIOVal wrap(Object arg) { return new Pioval(this, arg); }

  /**
   * Used for `unsafeTrace`
   */
  public Object identity(Object arg) { return arg; }

  /**
   * <pre>IO ::= val::Integer i::IO</pre>
   */
  public IOToken exit(int status) { throw new SilverExit(status); }

  /**
   * <pre>IO ::= s::String i::IO</pre>
   */
  public IOToken print(StringCatter str) {
    // TODO: Should we avoid demanding StringCatter objects?
    System.out.print(str.toString());
    return this;
  }

  /**
   * <pre>IO ::= s::String i::IO</pre>
   */
  public IOToken eprint(StringCatter str) {
    // TODO: Should we avoid demanding StringCatter objects?
    System.err.print(str.toString());
    return this;
  }

  // Used by readLineStdin
  private static BufferedReader our_stdin = null;
  /**
   * <pre>IOVal<String> ::= i::IO</pre>
   */
  public NIOVal readLineStdin() {
    try {
      if (our_stdin == null) {
        // Persist this, since it might buffer bytes for the NEXT line
        our_stdin = new BufferedReader(new InputStreamReader(System.in));
      }
      String line = our_stdin.readLine();
      if (line == null)
        return this.wrap(new Pnothing());
      else
        return this.wrap(new Pjust(new StringCatter(line)));
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
   */
  public NIOVal mkdir(StringCatter filepath) {
    return this.wrap(new File(filepath.toString()).mkdirs());
  }

  /**
   * Invokes an external command, channeling all stdin/out/err to the console
   * normally.
   *
   * N.B. uses 'bash' to invoke the command. There are two major reasons:
   * (1) allows redirects in shell command, which is useful
   * (2) because this command takes just a single string, we must somehow deal
   * with spaces. e.g. 'touch "abc 123"' bash take care of interpreting the
   * quotes for us.
   *
   * Unfortunate platform dependency though.
   *
   * <pre>IOVal<Integer> ::= s::String i::IO</pre>
   *
   * @param shell_command A string for back to interpret and execute.
   * @return The exit status of the process.
   */
  public NIOVal system(StringCatter shell_command) {
    try {
      ProcessBuilder pb =
          new ProcessBuilder("bash", "-c", shell_command.toString());
      pb.inheritIO();
      Process p = pb.start();
      return this.wrap(p.waitFor());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  /**
		}
	}

	/**
	 * <pre>IO ::= file::String contents::String i::IO</pre>
	 */
	public IOToken writeFile(StringCatter filename, StringCatter content) {
		return writeFileActual(filename, content, false);
	}

	/**
	 * <pre>IOVal<ByteArray> ::= s::String i::IO</pre>
	 */
	public NIOVal readByteFile(StringCatter filename) {
		try {
			Path path = Paths.get(filename.toString());
      		byte[] data = Files.readAllBytes(path);
      		return this.wrap(data);
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IO ::= file::String contents::ByteArray i::IO</pre>
	 */
	public IOToken writeByteFile(StringCatter filename, byte[] content) {
		try {
			File outputFile = new File(filename.toString());
			try (FileOutputStream outputStream = new FileOutputStream(outputFile)) {
				outputStream.write(content);
				outputStream.flush();
			}
			return this;
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IO ::= file::String contents::String i::IO</pre>
	 */
	public IOToken appendFile(StringCatter filename, StringCatter content) {
		return writeFileActual(filename, content, true);
	}

	// Used by writeFile and appendFile
	private IOToken writeFileActual(StringCatter filename, StringCatter content, boolean append) {
		try {
			Writer fout = new BufferedWriter(new FileWriter(filename.toString(), append));
			content.write(fout);
			fout.close();
			return this;
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IOVal<Integer> ::= s::String i::IO</pre>
	 */
	public NIOVal fileTime(StringCatter filename) {
		int modtime = (int) ((new File(filename.toString()).lastModified()) / 1000); 
		return this.wrap(modtime);
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
	 */
	public NIOVal isFile(StringCatter filename) {
		return this.wrap(new File(filename.toString()).isFile());
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
	 */
	public NIOVal isDirectory(StringCatter filename) {
		return this.wrap(new File(filename.toString()).isDirectory());
	}

	/**
	 * <pre>IOVal<String> ::= s::String i::IO</pre>
	 */
	public NIOVal readFile(StringCatter filename) {
		try {
			byte[] b = Files.readAllBytes(Paths.get(filename.toString()));
			return this.wrap(new StringCatter(new String(b)));
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
	 */
	public NIOVal isJarFile(StringCatter filename) {
        try {
			Path path = Paths.get(filename.toString());
			// Check if the file exists
			if (!Files.exists(path)) {
				return this.wrap(false);
			}
            // Check if the file's content-type is 'application/java-archive'
            String contentType = Files.probeContentType(path);
            return this.wrap(contentType != null && contentType.equals("application/java-archive"));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String e::String i::IO</pre>
	 */
	public NIOVal jarContainsEntry(StringCatter jarfile, StringCatter entry) {
		try {
			// Check if the entry exists in the jar file
			try (JarFile jar = new JarFile(jarfile.toString())) {
				return this.wrap(jar.getEntry(entry.toString()) != null);
			}
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IOVal<ByteArray> ::= s::String e::String i::IO</pre>
	 */
	public NIOVal readByteJarEntry(StringCatter jarfile, StringCatter entry) {
		try {
			// Read the entry from the jar file
			try (JarFile jar = new JarFile(jarfile.toString())) {
				try (InputStream is = jar.getInputStream(jar.getEntry(entry.toString()))) {
					byte[] b = is.readAllBytes();
					return this.wrap(b);
				}
			}
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IOVal<String> ::= i::IO</pre>
	 */
	public NIOVal cwd() {
		// Below is a typical approach because JVMs don't change the working directory.
		// However, if this fails to work in the future, here is an alternative approach:
		// Paths.get(".").toAbsolutePath().normalize().toString()
		
		return this.wrap(new StringCatter(System.getProperty("user.dir")));
	}
	
	/**
	 * <pre>IOVal<String> ::= s::String i::IO</pre>
	 */
	public NIOVal envVar(StringCatter env_var) {
		String result = System.getenv(env_var.toString());
		if (result == null)
			result = "";
		return this.wrap(new StringCatter(result));
	}

	/**
	 * <pre>IOVal<[String]> ::= s::String i::IO</pre>
	 */
	public NIOVal listContents(StringCatter filename) {
		try {
			File f = new File(filename.toString());
			String[] files = f.list();

			ConsCell result = ConsCell.nil;

			if(files != null) {
				for (String file : files) {
					result = new ConsCell(new StringCatter(file), result);
				}
			}

			return this.wrap(result);
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
	 */
	public NIOVal deleteFile(StringCatter filename) {
		return this.wrap(new File(filename.toString()).delete());
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::[String] i::IO</pre>
	 */
	public NIOVal deleteFiles(ConsCell files) {
		boolean result = true;
		while(!files.nil()) {
			StringCatter f = (StringCatter)files.head();
			result = result && new File(f.toString()).delete();
			files = files.tail();
		}
		return this.wrap(result);
	}

	/**
	 * <pre>IOVal<Boolean> ::= s::String i::IO</pre>
	 */
	public NIOVal deleteDirFiles(StringCatter dir) {
		try {
			File dirf = new File(dir.toString());
			String[] files = dirf.list();

			boolean result = true;

			if(files != null) {
				for(String filename : files) {
					File file = new File(dirf, filename);
					// Only files, no directories
					if(file.isFile()) {
						result = result && file.delete();
					}
				}
			}

			return this.wrap(result);
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IO ::= s::String  i::IO</pre>
	 */
	public IOToken deleteTree(StringCatter path) {
		// We should consider using walkFileTree, in the future
		deleteTreeRecursive(Paths.get(path.toString()));
		return this;
	}
	
	// Used by deleteTree
	private static void deleteTreeRecursive(Path f) {
		if(!Files.exists(f, LinkOption.NOFOLLOW_LINKS)) {
			// If the file doesn't exist, ignore it silently. Disk changed underneath us or something?
			// NOFOLLOW because we care if the symlink exists, not what the symlink points to.
			return;
		}
		// Just in case, we should never be trying to delete "/" or "/home" or "c:/users" etc.
		if(f.toAbsolutePath().normalize().toString().length() < 9)
			throw new RuntimeException("Canary against deleting things we shouldn't. Tried to delete path: " + f);
		try {
			// Need to handle: symlinks, directories, and normal files.
			if(Files.isSymbolicLink(f)) {
				// Deletes symlink, without traversing into it.
				Files.delete(f);
			} else if(Files.isDirectory(f)) {
				// Recursively delete files, then the directory itself.
				try (DirectoryStream<Path> stream = Files.newDirectoryStream(f)) {
					for (Path child : stream) {
						deleteTreeRecursive(child);
					}
				}
			} else {
				Files.delete(f);
			}
		} catch (IOException e) {
			// If we encounter an IO error anywhere, we immediately stop and raise an exception
			// Safety valve if we try to delete something we shouldn't.
			throw new RuntimeException(e);
		}
	}

	/**
	 * <pre>IO ::= src::String  dst::String  i::IO</pre>
	 */
	public IOToken copyFile(StringCatter from, StringCatter to) {
		Path src = Paths.get(from.toString());
		Path dst = Paths.get(to.toString());
		try {
			// copy 'x.java' into 'dst/'. Create the file 'dst/x.java'.
			// Works even if dst is a symlink.
			if(Files.isDirectory(dst)) {
				dst = dst.resolve(src.getFileName());
			}
			Files.copy(src, dst);
			return this;
		} catch (IOException io) {
			throw new RuntimeException(io);
		}
	}

	/**
	 * <pre>IO ::= file::String i::IO</pre>
	 */
	public IOToken touchFile(StringCatter filename) {
		setFileTime(filename, currentTime());
		return this;
	}

	/**
	 * <pre>IO ::= files::[String] i::IO</pre>
	 */
	public IOToken touchFiles(ConsCell files) {
		while(!files.nil()) {
			setFileTime((StringCatter)files.head(), currentTime());
			files = files.tail();
		}
		return this;
	}

	// Used by touchFile(s)
	private static void setFileTime(StringCatter filename, int time) {
		new File(filename.toString()).setLastModified(((long)time) * 1000);
	}
	private static int currentTime() {
		return (int)(System.currentTimeMillis() / 1000);
	}

	/**
	 * <pre>IOVal<a> ::= r::RandomGen<a> i::IO</pre>
	 */
	public NIOVal runRandomGen(final OriginContext ctx, silver.core.NRandomGen r) {
		return this.wrap(common.RandomGen.runRandomGen(ctx, r));
	}

	@Override
	public TypeRep getType() {
		return new BaseTypeRep("silver:core:IO");
	}
}
