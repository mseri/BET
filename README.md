# Birkhoff's ergodic theorem in LEAN4

![Lean build](https://github.com/oliver-butterley/birkhoff/actions/workflows/build.yml/badge.svg)

This repository contains the output of our project
at the [Machine-Checked Mathematics Workshop](https://www.lorentzcenter.nl/machine-checked-mathematics.html)
at the Lorentz Center, 10-14 July 2023.

The project was developed with @marcolenci and Guillaume Dubach,
under the support and supervision of Sébastien Gouëzel.

## How to use

I am assuming you have already lean4 and mathlib4 installed.
If not, [start here](https://leanprover-community.github.io/).

To start your project, clone this repo with
```
git clone https://github.com/mseri/birkhoff.git
```
then enter the folder
```
cd birkhoff
```
and download mathlib's cache with
```
lake exe cache get
```

The project file is `Birkhoff.lean`.
