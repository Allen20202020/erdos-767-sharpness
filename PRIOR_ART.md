# Prior work and attribution

Review performed on 17 September 2026.

## Mathematical source

Xiaozheng Chen and Bo Ning,
[On Erdős Problem 767: Cycles with Chords](https://arxiv.org/abs/2609.15330),
version 1, submitted 14 September 2026. The exact scope here is
Construction 3.3 at a = k and Remark 3.4. Credit for the mathematics belongs
to these authors; the source is a preprint, not an organizer verdict.
Their paper builds on Tao Jiang's 2004 theorem and the work of Ma and Ning.
The paper is linked, not redistributed.

## Existing formalization

[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos767.lean)
already formalizes Jiang's equality when n ≥ 3k+3. Its lower construction
is the complete bipartite graph with side sizes k+1 and n−k−1. We explicitly
acknowledge that result despite the award catalog still saying Lean proof: No.

The existing source contains 1,579 lines in the root module and accompanying
graph lemmas. Its root module was inspected; it credits Tao Jiang and states
the 3k+3 threshold. It does not implement the new matching-join witness at
the critical order ceil((5k+1)/2)−1. This package provides that witness, its
exact edge count, and its avoidance proof. It does not present Jiang's
already formalized theorem as new work.

The predicate, rim/chord endpoint selection argument, and chord transport
argument were adapted from that Apache-2.0 source. Their original copyright
and credit are retained in the Lean header and NOTICE. The cycle counting
inequality, generic matching-join avoidance result, matching construction,
critical-order calculation and final labelled witness are new proof code
developed for this package. All depend on the pinned Mathlib library.

Award-repository issue and PR snapshots were searched for JSP-000628,
Erdős 767 and arXiv:2609.15330. GitHub code search for the arXiv identifier
with Lean language and targeted web searches returned no additional matching
formalization. Search indexing can be incomplete; this is a bounded prior-art
check and does not establish worldwide priority.

## Contributor and licensing

Prepared by the submitting GitHub account with OpenAI Codex assistance.
Formalization-contribution review only; no solving share is requested.
Proposed formalizer identity: `RECIPIENT-JSP000628-A`, confirmation pending.
The submitter has a direct interest in the review result. Contributor-run
checks are not an independent human referee attestation or organizer approval.

New code and documentation in this proof package are released under
Apache-2.0. Derived portions retain the original attribution. No third-party
paper, compiled Mathlib object, payment information, identity document or
private correspondence is included.
