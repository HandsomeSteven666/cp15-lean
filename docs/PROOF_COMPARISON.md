# Comparing the proofs for fifteen disks

[中文](PROOF_COMPARISON.zh-CN.md)

This note compares the [manuscript and formal development of this project](https://doi.org/10.5281/zenodo.23319941) with the work [announced by nor on October 11, 2026](https://nor-blog.pages.dev/posts/2026-10-11-circle-in-circle-packing-15-20/). The technical comparison uses the [public PDF and supplementary release](https://nor-git.pages.dev/circle-packing/) downloaded on October 15, 2026. It is a comparison of the arguments and supplied material, rather than an independent rerun of that release's complete verification driver.

## Common conclusions and mechanisms

Both proofs concern the classical regular pentagon with an outward square on each side. With unit disk radii, put

$$
B=\sqrt{6+2/\sqrt5+4\sqrt{1+2/\sqrt5}}.
$$

Both obtain the minimum container radius $1+B$ and uniqueness for fifteen disks up to rotations, reflections and relabeling. The nor work also treats $N=16,17,18,20$; this repository's main result concerns $N=15$.

The proofs share substantial mathematical ingredients: the radial threshold $b-4/b$, angular budgets, cyclic orders, finite subdivisions of closed intervals and a local five-cycle inequality. None of these shared ingredients by itself distinguishes this project from that work.

## 1. The initial global reduction

This project chooses an optimal configuration, first maximizing the boundary-center count $K$ and then $S=\sum_i\|p_i\|$. Single-center displacements of that representative give inner-radius bounds, strict blocking contacts and contacts on both open sides of a radial line. A strict blocker $y$ of a nonzero inner center $x$ satisfies

$$
\|x-y\|=2,\quad \langle y,x\rangle>\|x\|^2,
\quad \|y\|^2>\|x\|^2+4.
$$

Here $m$ counts inner centers without a contact with a boundary center. Sections 3–4 and Appendix A reduce the selected representative to $K=10,m=0$ through contact counting and geometric exclusions.

The nor proof starts with an arbitrary feasible configuration at the fixed radius $B$. It projects every center of radius at least $c(b)=b-4/b$ to the boundary without decreasing any distance. Angular occupation bounds and an auxiliary radial-layer argument bound the number of inner centers; finite calculations exclude six, seven and eight inner centers, leaving five inner and ten outer centers. See Lemmas 2.2, 2.6, 2.8 and Proposition 7.3 of that paper.

The threshold agrees, but the reductions retain different information: extremal contact conditions here, and a projection with a strict recovery argument there.

## 2. Orders and finite certificates

Both encode the outer-center counts between five successive inner centers by positive integer vectors summing to ten. There are 126 vectors and 16 representatives under cyclic shifts and reversal. The empty-gap counts $e_i$ used here correspond to nor's counts by $q_i=e_i+1$.

This project covers $[1.23,2.25]^5$ using boundary-gap and inner-angle budgets and positive directed-cycle witnesses. It retains the alternating order in $[1.68,1.72]^5$. The closed-box certificates have 52,790 nodes and 26,403 leaves; Lean checks both their soundness rules and their concrete data.

Proposition 7.4 of the nor paper starts from rational grid intervals covering $[0.281,2.221]^5$. Radius contraction, chain-angle bounds and directed angle closure retain $q=(2,2,2,2,2)$ in $[1.693,1.709]^5$. The paper reports 63,846 boxes examined, with 175 accepted. Different starting domains, subdivisions and stopping conditions make these counts unsuitable as a direct efficiency comparison.

## 3. The shared five-cycle mechanism and different estimates

In common notation, both proofs control an angular cost of the form

$$
L_B(r)=\sum_{i=0}^{4}\max\{\alpha_B+\Gamma_B(r_i)+\Gamma_B(r_{i+1}),\Delta(r_i,r_{i+1})\}.
$$

Here $\alpha_B$ is the minimum boundary-to-boundary angular separation, $\Gamma_B$ is the inner-to-outer angle requirement, and $\Delta$ is the inner-pair requirement. In nor's notation, $\alpha_B=2\eta$, $\Gamma_B=h$ and $\Delta=g$. Both use

$$
\sum_i|t_i+t_{i+1}|\ge\frac25\sum_i|t_i|
$$

to exclude nonzero radial perturbations. Both have reference inner radius $r_*=1/\sin(\pi/5)$.

This project proves rational first-derivative intervals on $[1.68,1.72]^5$ and applies the mean value theorem to obtain

$$
L_B(r)-2\pi\ge\frac3{250}\sum_i|r_i-r_*|.
$$

Nor's Lemmas 7.5–7.7 instead use relative perturbations $\xi_i=(r_i-r_*)/r_*$ with $|\xi_i|\le1/200$. Second-derivative bounds control the Taylor remainders, yielding a positive linear bound, which can be taken as $\frac16\sum_i|\xi_i|$. The scales and domains differ.

## 4. Equality for every optimal configuration

The initial extremal selection here controls a representative, so a further argument is needed for arbitrary optimal configurations. Section 8 uses the connected components of the full feasible configuration space, terminal representatives, local isolation of the candidate congruence orbit, and its closedness and relative openness. A rational grid certificate also proves unique completion of each missing candidate boundary center from the other fourteen centers. This prevents another component from entering the candidate component by a single-center boundary replacement and yields global uniqueness.

Nor's Section 7.7 first determines every projected coordinate from equality in the angle bounds. Each projected outer center touches an unchanged inner center. The strict projection statement of Lemma 2.3 then forces that outer center to have been on the boundary originally. Thus no center moved, and the original arbitrary feasible configuration is identified directly. Its fifteen-disk argument does not require the component and fourteen-center-completion steps used here.

## 5. Verification and the purpose of this repository

The nor supplementary release contains Python and C++17 programs, exact-arithmetic angle tables, certificate data and a completed verification record. Its 71 archive entries contain no Lean source or Lean build configuration. This statement concerns the examined release, rather than an exhaustive search for every other formalization.

This development connects the geometric reductions and mathematical soundness of the certificates to three Lean endpoints:

```lean
CP15.centerOptimal_candidate
CP15.originalValue_eq_candidate
CP15.global_unique_optimal_packing15
```

On October 15, 2026, `lake build CP15` completed successfully with 9,148 jobs. Running `tools/SubmissionAudit.lean` printed the types and axiom dependencies of all three endpoints. Each depends only on `propext`, `Classical.choice` and `Quot.sound`. The global uniqueness endpoint quantifies over every fifteen-center configuration satisfying the radius and pairwise-separation bounds. Its conclusion supplies a relabeling and a centered linear isometry to the candidate; its type has no additional geometric exclusion hypothesis.

The repository provides reproducible theorem and certificate checking. Its extremal selection, strict-contact analysis and connected-component route to uniqueness also distinguish its proof organization. The shared angular and five-cycle mechanisms should be recognized as common ground between the developments.

## Source guide

Paths are relative to the Lean project root.

| Topic | Files or modules |
| --- | --- |
| Original problem and optimality definitions | `CP15/Definitions.lean`, `CP15/Original.lean` |
| Selected representatives and actual cyclic model | `CP15/SelectedFrontier.lean`, `CP15/SelectedK10Model.lean` |
| Soundness of finite covers | `CP15/K10ModelCover.lean`, `CP15/K10CoverChunk*.lean` |
| Local inequality and actual equality | `CP15/ExpandedLocalStability.lean`, `CP15/K10ActualGapEquality.lean` |
| Global optimality | `CP15/GlobalEndpoint.lean` |
| Components, completion and final uniqueness | `CP15/ComponentAscent.lean`, `CP15/UniqueExtensionOrbit.lean`, `CP15/GlobalUniquenessEndpoint.lean` |

The personal account and project timeline are in the [author's note](AUTHOR_NOTE.md).
