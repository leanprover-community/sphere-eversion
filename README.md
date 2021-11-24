# The sphere eversion project

The goal of this project is to formalize the proof of a theorem implying the existence of sphere eversions. Details can be found on the [project website.](https://leanprover-community.github.io/sphere-eversion/)

# Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To obtain this repo, run `leanproject get sphere-eversion`. If you already have the repo, you can
update it with `git pull` followed by `leanproject get-mathlib-cache`.

To build the repo, run `leanproject build`.

# Build the blueprint

To build the web version of the blue print, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip3 install invoke pandoc
cd .. # go to folder where you are happy clone git repos
git clone git@github.com:plastex/plastex
pip3 install ./plastex
git clone git@github.com:PatrickMassot/leanblueprint
pip3 install ./leanblueprint
cd sphere-eversion
```

To actually build the blueprint, run
```
leanproject get-mathlib-cache
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.