# Prover9 and Mace4 -- LADR-2026

Jeffrey Machado and Larry Lesyna present a backwards compatible, comprehensive modernization of William McCune’s Prover9 and Mace4 within the LADR framework.  Prover9 is an automated theorem prover for first-order and equational logic, and Mace4 searches for finite models and counterexamples.

This work preserves the original paramodulation calculus and intended inference rules of Prover9. The focus has been on stability, scalability, infrastructure alignment with contemporary ATP standards, and rigorous empirical validation.

---

## Engineering Modernization

The modernization effort addresses long-standing implementation constraints to better serve modern hardware:

- **Iterative Conversion:** Systematic conversion of deep recursive components to iterative implementations, eliminating stack overflows on large derivations.
- **Integer & Indexing Audit:** Full audit and correction of fixed-size integer handling and internal indexing structures.
- **Expanded Scaling:** Removal of legacy constraints; input capacity has been extended to greater than 100,000 formulas.
- **Fault Tolerance:** Correction of historical clause-handling defects to ensure robustness.
- **State Management:** Deterministic, architecture-neutral checkpoint and restore capability.

**Drop-in Compatibility:** By default, LADR-2026 produces identical search behavior to McCune's original LADR-2009-11A. Two optional clause-handling improvements are available via `set(back_subsume_skip_used)` and `set(back_subsume_skip_limbo)`. When enabled, these may alter proof search timing or derivation structure but do not change the underlying calculus.

---

## Performance & Benchmarks

- **Reliability:** Across 13,000+ TPTP problems, the system executes without segmentation faults.
- **Throughput:** Preprocessing performance improved an order of magnitude on large inputs. Inference throughput increased by approximately 10-20% under fixed benchmark configurations.
- **Validation:** LADR-2026 solved multiple TPTP problems rated 1.00 difficulty. These proofs were verified via GDV and IVY.

---

## Native TPTP Integration

LADR-2026 provides direct support for native TPTP input and TSTP proof output. No translation layer is required; proof objects conform to standard formats used in the modern ATP ecosystem.

---

## Premise Selection and Strategy Portfolio

The system integrates:

- **SInE-based premise selection** for handling large-theory problems.
- **Strategy Portfolio:** A Machine Learning (ML) selection of complementary search configurations.
- **Multi-Threading and Time-Slicing** A hyper-visor like manager for Multi-Tasking and Time-Slicing ML strategies.

While the underlying calculus remains unchanged, these implementation-level orchestrations significantly expand the system's "solve" profile.

---

## Determinism and Reproducibility

In single-strategy mode, LADR-2026 is fully deterministic: identical inputs and configurations produce identical proofs.

In multi-tasking mode, multiple search configurations execute in parallel. In this mode, proof selection may be influenced by process scheduling; repeated runs may produce different (but independently verifiable) proofs. This does not alter calculus semantics or soundness. All reported benchmark results specify the execution mode used.

---

## Availability & Positioning

LADR-2026 is an implementation-level modernization of a historically significant engine. We welcome independent benchmarking and scrutiny.

- **License:** Open source under GPLv2, consistent with the original LADR license.
- **Artifacts:** Source code and build instructions are included in each release.
