TO INSTALL JSCERT

Go to the Resources/Tools/ directory to find the core_js_src.tar file. Untar it and then.

1) make init
2) make clean
3) edit settings.sh to reflect the directory where you have the coq binaries, this path should have a trailing slash in it !
4) copy settings.sh to the tlc directory
5) make -j 2
(this is to speed up make by asking it to use dual cores, or just 'make' to not use the dual core of your machine)
Ignore any warnings you get.

For a more thorough installation procedure, try going through the respective readme's for tlc, jscert

To open the source files, for development, type ./open.sh &
This opens coqide with all the source files loaded