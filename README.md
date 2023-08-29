# Recasting

This crate supplies the `Recast` and `Recaster` traits. These are currently intended for the
translation of arena indexes like those in the `triple_arena` crate, however they can be used for
any purpose of one-to-one recasting of values.

Currently, the traits need to be manually implemented, but there should be a macro in a future
version that will automate implementation.

This crate has "std" and "alloc" features that can be turned off
