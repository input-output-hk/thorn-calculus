Overview
========

The `thorn-calculus` library contains the Þ-calculus, which is a
general-purpose process calculus. The Þ-calculus is embedded in
Isabelle/HOL, using higher-order abstract syntax (HOAS). The use of HOAS
allows us to have the object language (the Þ-calculus) only deal with
the key features of process calculi, which are concurrency and
communication, and leave the treatment of local names, data,
computation, conditional execution, and repetition to the meta-language
(Isabelle/HOL).

The Þ-calculus strongly resembles the asynchronous π-calculus. Processes
communicate via asynchronous channels, which can be global or created
locally. Channels are first-class and can therefore be transmitted
through other channels, thus making them visible outside their original
scopes. This is the mobility feature pioneered by the (synchronous)
π-calculus.


Requirements
============

You need Isabelle2022 to use this Isabelle library. You can obtain
Isabelle2022 from the [Isabelle website][isabelle].

[isabelle]:
    https://isabelle.in.tum.de/
    "Isabelle"

In addition, you need the following Isabelle sessions:

  * [`ZFC_in_HOL`](https://www.isa-afp.org/entries/ZFC_in_HOL.html)
  * [`Equivalence_Reasoner`](https://github.com/input-output-hk/equivalence-reasoner)
  * [`Transition_Systems`](https://github.com/input-output-hk/transition-systems)


Setup
=====

To make this Isabelle library available to your Isabelle installation,
add the path of the `src` directory to the file
`$ISABELLE_HOME_USER/ROOTS`. You can find out the value of
`$ISABELLE_HOME_USER` by running the following command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF file that includes the documentation and
the code and places it in `$ISABELLE_BROWSER_INFO/IOG`. You can find out
the value of `$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO

The makefile specifies two targets: `properly`, which is the default,
and `qnd`. With `properly`, fake proofs (`sorry`) are not accepted; with
`qnd`, quick-and-dirty mode is used and thus fake proofs are accepted.
