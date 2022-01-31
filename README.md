
string_matching
===============

This is just a collection of for string matching algorithms in C++.

Rabin-Karp
automata/DFA
Knuth-Morris-Pratt
Boyer-Moore

It compiles
g++ -o stringmatching -ansi -pedantic main.cpp

valgrind says there are no memory errors but it does show a weird CRC mismatch thing
which I've seen a few times on different programs but doesn't seem to have anything to
do with my code and never seems to affect the programs output.

I've tested them by hand fairly thouroughly but I intend to add some
test cases and maybe alternate versions that give the line number and position
in the line rather than the absolute offset (0 is beginning of file).

Rabin-Karp, automata and KMP algorithms I based off the pseudo-code
in Inroduction to Algorithms, Corment et al (3rd Edition).

Boyer Moore I based off what used to be in the Wikipedia article(Summer '11).
I improved it (and used C++ instead of straight C) and am using the strong suffix rule.

Update 2019: iirc Boyer Moore has a bug that I never got around to fixing

This is MIT Licensed but obviously you probably shouldn't use these for anything
serious.
