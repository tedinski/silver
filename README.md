# Silver

Silver is an extensible attribute grammar system that support many
modern extensions to Knuth's original design.  These include
higher-order attributes, reference attributes, forwarding, aspects,
and collections attributes.  Its type system support parametric
polymorphism.  Silver is distributed with Copper, a parser and
context-aware scanner generator.

It is designed for the modular development of composable language
extensions, with language features and analyses to support this.

## Using silver

Silver requires Java 11, Ant 1.10.0, Bash, and wget. It can run on Linux, MacOS, and Windows Subsystem for Linux (WSL) in Windows 10.

See [The Silver Install Guide](http://melt.cs.umn.edu/silver/install-guide)
for detailed information on how to get Silver set up.

Silver is written in Silver, which means after cloning the GitHub
repository you still need the executable Java jar files. You can download
these by running the ``update`` script in this repository. This will do a
`git pull` to update, then download jars, and clear any files generated
by older versions of Silver. A one-stop-shop for updating after the
initial clone.

## Authors and contributors
Silver is currently developed and maintained by

* Lucas Kramer  (krame505@umn.edu)
* Eric Van Wyk  (evw@cs.umn.edu)

Past contributors include Ted Kaminski (tedinski@cs.umn.edu), Derek Bodin, Lijesh Krishnan, and Jimin Gao.

It is developed by the Minnesota Extensible Language Tools (MELT) Group
(http://melt.cs.umn.edu) at the Department of Computer Science and Engineering (https://cs.umn.edu) at the University of Minnesota (https://umn.edu).


## Websites and repositories

Software downloads, documentation, and related papers are available on the
Melt group web site at http://melt.cs.umn.edu/.

Information about Copper and sample language frameworks developed with
Silver can be found on the MELT Group web site at
http://melt.cs.umn.edu

Actively-developed versions of this software are available on GitHub at
https://github.com/melt-umn/silver.

Archival versions of this software are permanently available on the Data
Repository of the University of Minnesota at https://doi.org/10.13020/D6QX07.

Other software and artifacts are also archived there and can be
reached from this persistent link: http://hdl.handle.net/11299/206558.


## Acknowledgements
We are very grateful to the National Science Foundation, the McKnight
Foundation, DARPA, the University of Minnesota, and IBM for funding
different aspects of our research and the development of Silver and
Copper.


## Licensing
Silver and Copper are distributed under the GNU Lesser General Public
License.  See the files COPYING and COPYING.LESSER for details of
these licenses.  More information can be found at
http://www.gnu.org/licenses/.

