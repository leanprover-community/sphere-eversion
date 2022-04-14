---
title: The sphere eversion project
---
# What is it about?

The goal of this project is to formalize the proof of existence of
[sphere eversions](https://www.youtube.com/watch?v=wO61D9x6lNY)
using the [Lean theorem prover](https://leanprover.github.io/), 
mainly developed at [Microsoft Research](https://www.microsoft.com/en-us/research/) 
by [Leonardo de Moura](https://leodemoura.github.io/).
More precisely we want to formalize the full *h*-principle for open and
ample first order differential relations, and deduce existence of sphere
eversions as a corollary.

The main motivations are:

* Demonstrating the proof assistant can handle geometric topology, and
  not only algebra or abstract nonsense. Note that Fabian Immler and
  Yong Kiam Tan already pioneered this direction by formalizing
  Poincaré-Bendixon, but this project has much larger scale.
* Exploring new infrastructure for collaborations on formalization
  projects, using the [interactive blueprint](blueprint/index.html).
* Producing a bilingual informal/formal document by keeping the
  blueprint and the formalization in sync.

### Exploring and helping

The best way to get started is to read the blueprint introduction,
either in [pdf](blueprint.pdf) or [online](blueprint/sect0001.html).
Then have a look at the [dependency graph](blueprint/dep_graph_document.html),
paying special attention to blue items. 
Blue items are items that are ready to be formalized because their
dependencies are formalized.
For lemmas, a blue border means the statement is ready for formalization,
and a blue background means the proof is ready for formalization.

Once you spotted something to work on, make sure to discuss in on
[Zulip](https://leanprover.zulipchat.com/) before writing code.
Once you formalized something, make sure the blueprint is still up to
date, since it needs to evolve to its bilingual document final state.
