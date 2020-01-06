# mset

This crate provides a [multiset](https://en.wikipedia.org/wiki/Multiset) implementation for rust.

## Overview

A mset, multiset, or bag is a set that allows multiple occurances of an element. It supports many basic set operations, e.g. membership test, union, intersection, and difference.

This implementation is based on the builtin `HashMap`, with a nod to [wheerd's python multiset library](https://github.com/wheerd/multiset/).