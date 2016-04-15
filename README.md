# ModelStructure-HTS
formalization of model structures in Homotopy Type System (in Coq)

## Compilation ##

* This development compiles with Coq8.5
* To compile simply type
    * ``` ./configure ``` to produce the Makefile
    * ``` make ``` to compile

## Plugin Myrewrite ##

We use a plugin to force Coq to use some given term to rewrite
instead of the autogenerated "paths_internal_rew". See comments
in HTS/Overture.v for the details.

## Coq dpd-graph ##

To generate dependency graphs of the developement you will need
Coq dpd-graph, at least https://github.com/ybertot/coq-dpdgraph/commit/94e7db4ddb1f15cf46d17691cfc5375574053796
