# The sphere eversion project (supplementary material for CPP 2023)

This is the supplementary material for the CPP 2023 paper
"Formalising the h-principle and sphere eversion"

# Contents of this folder

The Lean source files are in the `src` directory, together with the compiled binaries.
The source files for the blueprint are in the `blueprint/src` directory.
A compiled pdf version is in `blueprint.pdf`. A compiled html version is in the
`blueprint/web` folder. We recommend using a local webserver to browse it
since otherwise some icons will be banned by browser security restrictions
(for instance using `python3 -m http.server` in the folder `blueprint/web` and then opening `localhost:8000` in your browser).

# Navigating the Lean files

To navigate the code and get feedback from Lean, one does need a working version of Lean.
See [the installation instructions of Lean](https://leanprover-community.github.io/get_started.html) (under Regular install).

One also needs the right version of mathlib. There are two options:
* download mathlib yourself by executing the following commands in the directory containing this `README.md`: `leanpkg configure` followed by `leanproject get-mathlib-cache`.
* download `mathlib.zip` that was made available together with `cpp2023.zip` and extract it in the same location as `cpp2023.zip`. You should have a root directory with contains (among other things) this `README.md` and a `_target` directory. Then run `leanproject get-mathlib-cache` in this root directory.

After obtaining mathlib, one can then build this project using `leanproject build`.
This should not do much, since the compiled binaries are already included.
It should only check that all files are compiled, and then exit after 10-20 seconds with only a few lines of output.

Next we give instructions on how to navigate the code using the VS code editor.
If you installed Lean using the aforementioned instructions,
you should have a working version of VS code with the Lean 3 extension.

To launch VS code, run `code .` in the top-level directory to open the project folder.
Opening a single file in VS Code will cause the extension to misbehave.
After opening a `.lean` file, there should be a `Lean infoview` on the right-hand side of your screen, which will give you information from Lean.
This can be used to navigate the proofs. You will be able to see goal states when putting your cursor in the middle of a proof, and you can obtain more information form the goal state by clicking on them.

To confirm that we have proven a theorem without additional axioms, you can run at
the bottom of `local/sphere_eversion.lean` the command `#print axioms sphere_eversion_of_loc`
to see which axioms are used. This should return the list `classical.choice`, `quot.sound`,
`propext`. If any proofs were omitted or additional axioms were used, they would be mentioned here.

# Build the blueprint html

The blueprint is already included in the supplementary material.
If you want to build it from scratch, you need a working LaTeX installation.
Furthermore, you need some packages:
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
leanproject build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.
