# A note from the author

[中文](AUTHOR_NOTE.zh-CN.md)

I began an independent study of the optimal packing of fifteen equal disks in a disk in September 2026. On October 6, I submitted my manuscript, *The optimal packing of fifteen congruent disks in a disk is unique*, to *Discrete & Computational Geometry*. On October 15, I made the manuscript and accompanying materials public on [Zenodo](https://doi.org/10.5281/zenodo.23319941).

 My training is in engineering rather than mathematics. Bringing a geometric problem that interested me to this stage, and turning the arguments for optimality and global uniqueness into checkable proofs, has been a source of considerable joy.

Today I learned that nor had publicly released [work covering fifteen, sixteen, seventeen, eighteen and twenty equal disks](https://nor-blog.pages.dev/posts/2026-10-11-circle-in-circle-packing-15-20/) on October 11. I am glad to see broader progress by someone who shares an interest in mathematics. I also felt disappointed to discover, after submitting my own manuscript, that related results had appeared before I made my preprint public. I value the experience of exploring and understanding this problem, and I do not want this repository to become an argument over credit.

I did not get a preprint online sooner, in part because of my limited English and the difficulties I encountered navigating the arXiv submission requirements. This experience has taught me that sharing work promptly and clearly is also part of doing research.

This repository is something I am still happy to share. It provides another proof route for the fifteen-disk problem and a Lean formalization of both the optimal radius and global uniqueness. The development connects the geometric definitions, configuration reductions, soundness of the finite certificates, equality analysis and global uniqueness. Readers can inspect the theorem statements, build the project and check the axiom dependencies themselves. The nor release that I examined on October 15, 2026 contains exact-arithmetic verification material in Python and C++, but no corresponding Lean sources. The [proof comparison](PROOF_COMPARISON.md) explains the relationship between the two developments.

I hope these materials will be useful to people studying the problem, learning to formalize geometry or reproducing the proofs. Making this work available for others to read, check and build on is meaningful to me. Questions, corrections and improvements are welcome.

Xiuzhi Yang  
October 15, 2026

## Submission record

The following two crops come from the same author-supplied submission-dashboard screenshot. Text inside the retained regions is unchanged. Account details, the manuscript identifier and the processing status have been omitted by cropping.

![Journal name on the submission dashboard](images/dcg-journal-header.png)

![Manuscript title and initial submission date: October 6, 2026](images/dcg-submission-date.png)

This manuscript was submitted to *Discrete & Computational Geometry* on October 6, 2026.
