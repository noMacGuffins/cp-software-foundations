
# Installation (vscode, Mac Intel silicon)
1. In order to use vscoq, install through opam (do not install through coq platform)
    ~~~
    opam pin add coq 8.18.0
    opam install vscoq-language-server
    ~~~
 2. Check if vscoq was installed correctly 
    ~~~
    which vscoqtop
    ~~~
3. Turn vscode on and install the VsCoq extension.
4. Reload vscode
5. Open project directory and run!

# Build and Testing
1. Open the directory of the volume to work on in vscode (do not open the root directory or else vscoq will not recognize each variables... Its fine if you'll only be using the terminal.)
1. Clean the directory
    ~~~
    make clean
    ~~~
2. Add files to compile in _CoqProject
3. Build
    ~~~
    make
    ~~~
4. Check console for grades and comments.

