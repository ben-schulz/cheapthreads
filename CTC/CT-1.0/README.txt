This is ~/cheapthreads/CTC/CT/CT-1.0

A cleaned-up version of Adam's CT front-end, together with a cleaned-up
version and much more principled implementation of the CT defunctionalizer
back-end.

This is a personal fun-with-coding side-project started 2009.12.30,
and is presently ongoing.

Top-level testing functions are in ./Test.hs

An assortment of test programs (and miscellany) is in ./TestPrograms/

Stable phases of the compiler are invoked by loading Test and
invoking the compilation function at the ghci prompt as:

  ctc opt file_path

where 'opt' is a string of possible options (usually the empty string,
indicating the defaults) and 'file_path' is the input file.

More documentation can be found in the various *.log.txt files.

-- Schulz
