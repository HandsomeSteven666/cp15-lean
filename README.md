# CP15: optimality and global uniqueness in Lean

[中文说明](docs/AUTHOR_NOTE.zh-CN.md) · [Author's note](docs/AUTHOR_NOTE.md) · [Proof comparison](docs/PROOF_COMPARISON.md)

Lean 4 sources for the optimal packing of fifteen congruent unit disks in a disk, including the equality case and global uniqueness up to rotations, reflections and relabeling.

The manuscript and accompanying material are available on [Zenodo](https://doi.org/10.5281/zenodo.23319941). The manuscript was submitted to *Discrete & Computational Geometry* on October 6, 2026 and made public on Zenodo on October 15, 2026. It is a preprint, not an accepted journal publication.

## Mathematical result

Let

$$
B=\sqrt{6+2/\sqrt5+4\sqrt{1+2/\sqrt5}}.
$$

The smallest container radius for fifteen unit disks with disjoint interiors is $1+B$. The centers are the five vertices of a regular pentagon of side two and the ten additional vertices of the outward square on each side. Every optimal configuration is congruent to this construction, allowing relabeling and an orthogonal transformation about the container center.

The three final endpoints are:

| Lean declaration | Mathematical statement |
| --- | --- |
| `CP15.centerOptimal_candidate` | `B` is the least feasible center radius with pairwise separation at least two. |
| `CP15.originalValue_eq_candidate` | The maximum minimum distance of fifteen points in the unit disk is `2 / B`. |
| `CP15.global_unique_optimal_packing15` | Every feasible fifteen-center configuration at radius `B` is centered-congruent to the candidate. |

The first two endpoints are in [GlobalEndpoint.lean](CP15/GlobalEndpoint.lean); the global uniqueness endpoint is in [GlobalUniquenessEndpoint.lean](CP15/GlobalUniquenessEndpoint.lean). The latter has the type

```lean
theorem global_unique_optimal_packing15 :
    ∀ p : FeasiblePacking15 candidateB,
      CenteredCongruent15 p.1 Candidate.pointAtSeparationTwo
```

`FeasiblePacking15` requires all center norms to be at most `candidateB` and all distinct pairs to be at distance at least two. `CenteredCongruent15` supplies a permutation and a real linear isometry. The final declarations have no extra geometric-exclusion or rigidity assumptions.

## Build and audit

Install [Lean through elan](https://github.com/leanprover/elan). The checked-in `lean-toolchain` selects Lean **4.34.0**. Mathlib is pinned to commit `56a9a88447f391672d7aeea117da03b6f7016b0d`; `lake-manifest.json` pins its transitive dependencies.

```sh
git clone https://github.com/HandsomeSteven666/cp15-lean.git
cd cp15-lean
lake exe cache get
lake build CP15
lake env lean tools/SubmissionAudit.lean
```

In PowerShell, the supplied driver runs the same build and checks the three endpoint axiom lists:

```powershell
.\verify_submission.ps1
```

On October 15, 2026, the source project completed `lake build CP15` with **9,148 jobs** using its existing cache. The submission audit printed the theorem types and, for all three final endpoints, exactly these axiom dependencies:

```text
propext, Classical.choice, Quot.sound
```

This release's 224 Lean source files are byte-for-byte identical to those in the source archive deposited on Zenodo. The dated local build used existing dependency and build caches; it was not a clean build on a fresh machine. No GitHub-hosted CI result is claimed for the initial release.

## Proof organization

The proof chooses an extremal representative, derives strict contact and angular constraints, reduces to ten boundary centers and five inner centers, and checks a complete finite cover of the remaining scalar cases. A local angular inequality fixes the inner radii and actual angle gaps. A separate connected-component and unique-boundary-completion argument identifies every optimal configuration.

| Part | Entry points |
| --- | --- |
| Original definitions and scaling | [Definitions](CP15/Definitions.lean), [Original](CP15/Original.lean), [Scaling](CP15/Scaling.lean) |
| Selection and contacts | [CompactSelection](CP15/CompactSelection.lean), [SelectedFrontier](CP15/SelectedFrontier.lean) |
| Cyclic geometry and finite covers | [SelectedK10Model](CP15/SelectedK10Model.lean), [K10ModelCover](CP15/K10ModelCover.lean) |
| Local inequality and equality | [ExpandedLocalStability](CP15/ExpandedLocalStability.lean), [K10ActualGapEquality](CP15/K10ActualGapEquality.lean) |
| Global uniqueness | [ComponentAscent](CP15/ComponentAscent.lean), [GlobalUniquenessTerminalReference](CP15/GlobalUniquenessTerminalReference.lean), [GlobalUniquenessEndpoint](CP15/GlobalUniquenessEndpoint.lean) |

The `K10CoverChunk*.lean` modules contain generated certificate data as Lean theorem sources. They are proof inputs and must remain in the repository. Replaying the proof checks these sources directly; it does not require rerunning the external programs that originally proposed the data.

## Related work and author

On October 11, 2026, nor [announced work for 15, 16, 17, 18 and 20 disks](https://nor-blog.pages.dev/posts/2026-10-11-circle-in-circle-packing-15-20/), including optimality and uniqueness for fifteen disks. The arguments share substantial angular and five-cycle mechanisms. Their global reductions, local estimates and routes to uniqueness differ. See the [detailed comparison](docs/PROOF_COMPARISON.md) ([中文](docs/PROOF_COMPARISON.zh-CN.md)).

The project used AI assistance during proof development and exposition. The theorem statements and proof terms are available for independent checking in Lean.

I am Xiuzhi Yang, an undergraduate at Anhui University of Science and Technology, enrolled in 2024 in ammunition engineering and explosive technology. My [personal note](docs/AUTHOR_NOTE.md) ([中文](docs/AUTHOR_NOTE.zh-CN.md)) describes the project and includes cropped extracts of the October 6 submission record.

## License and citation

The original project material is distributed under [CC BY 4.0](LICENSE.md), consistent with the Zenodo release. Imported dependencies are not vendored here and retain their respective licenses. The submission screenshots contain third-party interface and journal branding; their inclusion documents the submission record and does not grant rights to that branding.

Please cite the [Zenodo manuscript and source deposit](https://doi.org/10.5281/zenodo.23319941). A machine-readable citation is in [CITATION.cff](CITATION.cff).
