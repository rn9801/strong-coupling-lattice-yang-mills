/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.OrderedPartitionMobius

/-!
# Coarsenings of a finite partition

A coarsening of a finite partition `Q` is exactly a partition of the finite
set `Q.parts`.  This file constructs the forward map needed by the connected
graph cancellation and proves that it preserves the number of parts.  The
construction uses literal fibers of the unique coarser part containing each
part of `Q`, avoiding quotient carriers.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite partition coarser than `Q`. -/
abbrev FinpartitionCoarsening
    (Q : Finpartition (Finset.univ : Finset α)) :=
  {R : Finpartition (Finset.univ : Finset α) // Q ≤ R}

/-- The unique part of a coarsening which contains a given part of the finer
partition. -/
def finpartitionCoarseningTarget
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (q : Q.parts) : R.1.parts :=
  ⟨Classical.choose (R.2 q.2), (Classical.choose_spec (R.2 q.2)).1⟩

theorem finpartitionCoarseningTarget_contains
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (q : Q.parts) :
    q.1 ⊆ (finpartitionCoarseningTarget Q R q).1 :=
  (Classical.choose_spec (R.2 q.2)).2

theorem finpartitionCoarseningTarget_eq_of_subset
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (q : Q.parts) (t : R.1.parts)
    (hqt : q.1 ⊆ t.1) :
    finpartitionCoarseningTarget Q R q = t := by
  apply Subtype.ext
  obtain ⟨v, hvq⟩ := Q.nonempty_of_mem_parts q.2
  exact R.1.eq_of_mem_parts
    (finpartitionCoarseningTarget Q R q).2 t.2
    (finpartitionCoarseningTarget_contains Q R q hvq) (hqt hvq)

theorem finpartitionCoarseningTarget_surjective
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    Function.Surjective (finpartitionCoarseningTarget Q R) := by
  intro t
  obtain ⟨v, hvt⟩ := R.1.nonempty_of_mem_parts t.2
  obtain ⟨q, hq, hvq⟩ := Q.exists_mem (Finset.mem_univ v)
  let q' : Q.parts := ⟨q, hq⟩
  refine ⟨q', ?_⟩
  exact finpartitionCoarseningTarget_eq_of_subset Q R q' t <| by
    intro w hwq
    have htarget := finpartitionCoarseningTarget_contains Q R q' hwq
    have hvtarget := finpartitionCoarseningTarget_contains Q R q' hvq
    have heq : (finpartitionCoarseningTarget Q R q').1 = t.1 :=
      R.1.eq_of_mem_parts
        (finpartitionCoarseningTarget Q R q').2 t.2 hvtarget hvt
    rwa [heq] at htarget

/-- Fiber of the map from fine parts to coarser parts. -/
def finpartitionCoarseningFiber
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (t : R.1.parts) : Finset Q.parts :=
  Finset.univ.filter fun q ↦ finpartitionCoarseningTarget Q R q = t

@[simp]
theorem mem_finpartitionCoarseningFiber
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (t : R.1.parts) (q : Q.parts) :
    q ∈ finpartitionCoarseningFiber Q R t ↔
      finpartitionCoarseningTarget Q R q = t := by
  simp [finpartitionCoarseningFiber]

theorem finpartitionCoarseningFiber_nonempty
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (t : R.1.parts) :
    (finpartitionCoarseningFiber Q R t).Nonempty := by
  obtain ⟨q, hq⟩ := finpartitionCoarseningTarget_surjective Q R t
  exact ⟨q, (mem_finpartitionCoarseningFiber Q R t q).mpr hq⟩

theorem finpartitionCoarseningFiber_injective
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    Function.Injective (finpartitionCoarseningFiber Q R) := by
  intro t u htu
  obtain ⟨q, hqt⟩ := finpartitionCoarseningFiber_nonempty Q R t
  have hqu : q ∈ finpartitionCoarseningFiber Q R u := htu ▸ hqt
  exact ((mem_finpartitionCoarseningFiber Q R t q).mp hqt).symm.trans
    ((mem_finpartitionCoarseningFiber Q R u q).mp hqu)

/-- A coarsening induces a partition of the finite set of fine parts. -/
def finpartitionCoarseningIndexPartition
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    Finpartition (Finset.univ : Finset Q.parts) := by
  classical
  let parts : Finset (Finset Q.parts) :=
    Finset.univ.image (finpartitionCoarseningFiber Q R)
  refine Finpartition.ofExistsUnique parts (fun _ _ _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro q _
    let t := finpartitionCoarseningTarget Q R q
    refine ⟨finpartitionCoarseningFiber Q R t, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    · exact (mem_finpartitionCoarseningFiber Q R t q).mpr rfl
    · intro b hb
      obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hb.1
      apply congrArg (finpartitionCoarseningFiber Q R)
      exact ((mem_finpartitionCoarseningFiber Q R u q).mp hb.2).symm
  · intro hempty
    obtain ⟨t, _ht, ht⟩ := Finset.mem_image.mp hempty
    exact (finpartitionCoarseningFiber_nonempty Q R t).ne_empty ht

@[simp]
theorem parts_finpartitionCoarseningIndexPartition
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    (finpartitionCoarseningIndexPartition Q R).parts =
      Finset.univ.image (finpartitionCoarseningFiber Q R) :=
  rfl

/-- Passing to the partition of fine parts preserves the number of coarser
parts exactly. -/
theorem card_parts_finpartitionCoarseningIndexPartition
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    (finpartitionCoarseningIndexPartition Q R).parts.card = R.1.parts.card := by
  rw [parts_finpartitionCoarseningIndexPartition,
    Finset.card_image_of_injective _
      (finpartitionCoarseningFiber_injective Q R)]
  simp

/-- Union in the original carrier of a collection of parts of `Q`. -/
def finpartitionGroupUnion
    (Q : Finpartition (Finset.univ : Finset α))
    (B : Finset Q.parts) : Finset α :=
  B.biUnion fun q ↦ q.1

@[simp]
theorem mem_finpartitionGroupUnion
    (Q : Finpartition (Finset.univ : Finset α))
    (B : Finset Q.parts) (v : α) :
    v ∈ finpartitionGroupUnion Q B ↔ ∃ q ∈ B, v ∈ q.1 := by
  simp [finpartitionGroupUnion]

theorem finpartitionGroupUnion_nonempty
    (Q : Finpartition (Finset.univ : Finset α))
    {B : Finset Q.parts} (hB : B.Nonempty) :
    (finpartitionGroupUnion Q B).Nonempty := by
  obtain ⟨q, hqB⟩ := hB
  obtain ⟨v, hvq⟩ := Q.nonempty_of_mem_parts q.2
  exact ⟨v, (mem_finpartitionGroupUnion Q B v).mpr ⟨q, hqB, hvq⟩⟩

/-- A collection of parts of `Q` is determined by its union in the original
carrier. -/
theorem finpartitionGroupUnion_injective
    (Q : Finpartition (Finset.univ : Finset α)) :
    Function.Injective (finpartitionGroupUnion Q) := by
  intro B C hBC
  ext q
  constructor
  · intro hqB
    obtain ⟨v, hvq⟩ := Q.nonempty_of_mem_parts q.2
    have hvC : v ∈ finpartitionGroupUnion Q C := by
      rw [← hBC]
      exact (mem_finpartitionGroupUnion Q B v).mpr ⟨q, hqB, hvq⟩
    obtain ⟨r, hrC, hvr⟩ :=
      (mem_finpartitionGroupUnion Q C v).mp hvC
    have hqr : q = r := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts q.2 r.2 hvq hvr
    exact hqr ▸ hrC
  · intro hqC
    obtain ⟨v, hvq⟩ := Q.nonempty_of_mem_parts q.2
    have hvB : v ∈ finpartitionGroupUnion Q B := by
      rw [hBC]
      exact (mem_finpartitionGroupUnion Q C v).mpr ⟨q, hqC, hvq⟩
    obtain ⟨r, hrB, hvr⟩ :=
      (mem_finpartitionGroupUnion Q B v).mp hvB
    have hqr : q = r := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts q.2 r.2 hvq hvr
    exact hqr ▸ hrB

/-- Group the parts of `Q` according to a partition of the finite type
`Q.parts`. -/
def finpartitionGrouping
    (Q : Finpartition (Finset.univ : Finset α))
    (A : Finpartition (Finset.univ : Finset Q.parts)) :
    Finpartition (Finset.univ : Finset α) := by
  classical
  let parts : Finset (Finset α) :=
    A.parts.image (finpartitionGroupUnion Q)
  refine Finpartition.ofExistsUnique parts (fun _ _ _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro v _
    obtain ⟨q, hq, hvq⟩ := Q.exists_mem (Finset.mem_univ v)
    let q' : Q.parts := ⟨q, hq⟩
    obtain ⟨B, hBA, hqB⟩ := A.exists_mem (Finset.mem_univ q')
    refine ⟨finpartitionGroupUnion Q B, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨B, hBA, rfl⟩
    · exact (mem_finpartitionGroupUnion Q B v).mpr ⟨q', hqB, hvq⟩
    · intro t ht
      obtain ⟨C, hCA, rfl⟩ := Finset.mem_image.mp ht.1
      obtain ⟨r, hrC, hvr⟩ :=
        (mem_finpartitionGroupUnion Q C v).mp ht.2
      have hqr : q' = r := by
        apply Subtype.ext
        exact Q.eq_of_mem_parts q'.2 r.2 hvq hvr
      subst r
      exact congrArg (finpartitionGroupUnion Q)
        (A.eq_of_mem_parts hCA hBA hrC hqB)
  · intro hempty
    obtain ⟨B, hBA, hB⟩ := Finset.mem_image.mp hempty
    exact (finpartitionGroupUnion_nonempty Q
      (A.nonempty_of_mem_parts hBA)).ne_empty hB

@[simp]
theorem parts_finpartitionGrouping
    (Q : Finpartition (Finset.univ : Finset α))
    (A : Finpartition (Finset.univ : Finset Q.parts)) :
    (finpartitionGrouping Q A).parts =
      A.parts.image (finpartitionGroupUnion Q) :=
  rfl

/-- The grouped partition is a coarsening of the original partition. -/
def finpartitionGroupingCoarsening
    (Q : Finpartition (Finset.univ : Finset α))
    (A : Finpartition (Finset.univ : Finset Q.parts)) :
    FinpartitionCoarsening Q := by
  classical
  refine ⟨finpartitionGrouping Q A, ?_⟩
  intro q hq
  let q' : Q.parts := ⟨q, hq⟩
  let B : Finset Q.parts := A.part q'
  refine ⟨finpartitionGroupUnion Q B, ?_, ?_⟩
  · rw [parts_finpartitionGrouping]
    exact Finset.mem_image.mpr
      ⟨B, A.part_mem.mpr (Finset.mem_univ q'), rfl⟩
  · intro v hvq
    exact (mem_finpartitionGroupUnion Q B v).mpr
      ⟨q', A.mem_part (Finset.mem_univ q'), hvq⟩

/-- The union of a target fiber is exactly the corresponding coarser part. -/
theorem finpartitionGroupUnion_coarseningFiber
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) (t : R.1.parts) :
    finpartitionGroupUnion Q (finpartitionCoarseningFiber Q R t) = t.1 := by
  ext v
  constructor
  · intro hv
    obtain ⟨q, hqFiber, hvq⟩ :=
      (mem_finpartitionGroupUnion Q
        (finpartitionCoarseningFiber Q R t) v).mp hv
    have htarget :=
      (mem_finpartitionCoarseningFiber Q R t q).mp hqFiber
    have hvTarget := finpartitionCoarseningTarget_contains Q R q hvq
    exact htarget ▸ hvTarget
  · intro hvt
    obtain ⟨q, hq, hvq⟩ := Q.exists_mem (Finset.mem_univ v)
    let q' : Q.parts := ⟨q, hq⟩
    have htarget : finpartitionCoarseningTarget Q R q' = t := by
      apply Subtype.ext
      exact R.1.eq_of_mem_parts
        (finpartitionCoarseningTarget Q R q').2 t.2
        (finpartitionCoarseningTarget_contains Q R q' hvq) hvt
    exact (mem_finpartitionGroupUnion Q
      (finpartitionCoarseningFiber Q R t) v).mpr
        ⟨q', (mem_finpartitionCoarseningFiber Q R t q').mpr htarget, hvq⟩

/-- Grouping the fiber partition induced by a coarsening reconstructs that
coarsening exactly. -/
theorem finpartitionGrouping_coarseningIndexPartition
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    finpartitionGrouping Q (finpartitionCoarseningIndexPartition Q R) = R.1 := by
  apply Finpartition.ext
  ext r
  constructor
  · intro hr
    rw [parts_finpartitionGrouping] at hr
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hr
    rw [parts_finpartitionCoarseningIndexPartition] at hB
    obtain ⟨t, _ht, hBt⟩ := Finset.mem_image.mp hB
    rw [← hBt, finpartitionGroupUnion_coarseningFiber]
    exact t.2
  · intro hr
    rw [parts_finpartitionGrouping]
    let t : R.1.parts := ⟨r, hr⟩
    refine Finset.mem_image.mpr
      ⟨finpartitionCoarseningFiber Q R t, ?_, ?_⟩
    · rw [parts_finpartitionCoarseningIndexPartition]
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    · exact finpartitionGroupUnion_coarseningFiber Q R t

/-- The forward map from coarsenings to partitions of the fine-part set is
injective. -/
theorem finpartitionCoarseningIndexPartition_injective
    (Q : Finpartition (Finset.univ : Finset α)) :
    Function.Injective (finpartitionCoarseningIndexPartition Q) := by
  intro R T hRT
  apply Subtype.ext
  have hgrouped := congrArg (finpartitionGrouping Q) hRT
  rw [finpartitionGrouping_coarseningIndexPartition,
    finpartitionGrouping_coarseningIndexPartition] at hgrouped
  exact hgrouped

/-- Grouping partitions of the fine-part type is injective. -/
theorem finpartitionGrouping_injective
    (Q : Finpartition (Finset.univ : Finset α)) :
    Function.Injective (finpartitionGrouping Q) := by
  intro A B hAB
  apply Finpartition.ext
  have hparts := congrArg Finpartition.parts hAB
  exact Finset.image_injective (finpartitionGroupUnion_injective Q) hparts

/-- Taking target fibers after grouping recovers the original partition of
the fine-part type. -/
theorem finpartitionCoarseningIndexPartition_grouping
    (Q : Finpartition (Finset.univ : Finset α))
    (A : Finpartition (Finset.univ : Finset Q.parts)) :
    finpartitionCoarseningIndexPartition Q
        (finpartitionGroupingCoarsening Q A) = A := by
  apply finpartitionGrouping_injective Q
  rw [finpartitionGrouping_coarseningIndexPartition]
  rfl

/-- Coarsenings of `Q` are exactly partitions of the labelled finite type of
parts of `Q`. -/
def finpartitionCoarseningEquivIndexPartition
    (Q : Finpartition (Finset.univ : Finset α)) :
    FinpartitionCoarsening Q ≃
      Finpartition (Finset.univ : Finset Q.parts) where
  toFun := finpartitionCoarseningIndexPartition Q
  invFun := finpartitionGroupingCoarsening Q
  left_inv R := by
    apply Subtype.ext
    exact finpartitionGrouping_coarseningIndexPartition Q R
  right_inv := finpartitionCoarseningIndexPartition_grouping Q

/-- Canonically label the blocks of a coarsening partition by an ordered
finite partition. -/
noncomputable def finpartitionCoarseningEquivOrdered
    (Q : Finpartition (Finset.univ : Finset α)) :
    FinpartitionCoarsening Q ≃ OrderedFinpartition (Fintype.card Q.parts) :=
  (finpartitionCoarseningEquivIndexPartition Q).trans
    (orderedFinpartitionEquivFinpartitionOfFintype Q.parts).symm

@[simp]
theorem card_parts_eq_length_finpartitionCoarseningEquivOrdered
    (Q : Finpartition (Finset.univ : Finset α))
    (R : FinpartitionCoarsening Q) :
    R.1.parts.card = (finpartitionCoarseningEquivOrdered Q R).length := by
  let e := orderedFinpartitionEquivFinpartitionOfFintype Q.parts
  let c := finpartitionCoarseningEquivOrdered Q R
  have hcard :=
    card_parts_orderedFinpartitionEquivFinpartitionOfFintype Q.parts c
  have heq : e c = finpartitionCoarseningIndexPartition Q R := by
    change e (e.symm (finpartitionCoarseningIndexPartition Q R)) =
      finpartitionCoarseningIndexPartition Q R
    exact e.apply_symm_apply _
  rw [heq, card_parts_finpartitionCoarseningIndexPartition] at hcard
  exact hcard

noncomputable instance instFintypeFinpartitionCoarsening
    (Q : Finpartition (Finset.univ : Finset α)) :
    Fintype (FinpartitionCoarsening Q) :=
  Fintype.ofFinite _

/-- Möbius cancellation over all coarsenings of a fixed finite partition. -/
theorem sum_finpartitionCoarsening_topMobiusWeight
    (Q : Finpartition (Finset.univ : Finset α)) :
    (∑ R : FinpartitionCoarsening Q,
      partitionMobiusBlockWeight R.1.parts.card) =
      if Q.parts.card = 0 ∨ Q.parts.card = 1 then 1 else 0 := by
  classical
  let e := finpartitionCoarseningEquivOrdered Q
  rw [← e.symm.sum_comp]
  simp only [Equiv.symm_apply_apply, e,
    card_parts_eq_length_finpartitionCoarseningEquivOrdered,
    orderedFinpartitionTopMobiusWeight]
  simpa using
    sum_orderedFinpartitionTopMobiusWeight (Fintype.card Q.parts)

end

end YangMills.Polymer
