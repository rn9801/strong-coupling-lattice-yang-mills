/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Partition.Finpartition

/-!
# Ordered and unordered finite partitions of `Fin n`

Mathlib's `OrderedFinpartition n` is the canonical labelled-set partition
used by Faà di Bruno, whereas finite graph cumulants use
`Finpartition (Finset.univ : Finset (Fin n))`.  This file proves that the two
types are equivalent.  A block is parameterized increasingly, and blocks are
ordered by their largest elements, exactly as in `OrderedFinpartition`.

This is finite-set combinatorics only; it has no polymer or Yang--Mills
dependency.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- The literal finset carried by one block of an ordered finite partition. -/
def orderedFinpartitionBlock {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) : Finset (Fin n) :=
  Finset.univ.map ⟨c.emb i, (c.emb_strictMono i).injective⟩

@[simp]
theorem mem_orderedFinpartitionBlock {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) (v : Fin n) :
    v ∈ orderedFinpartitionBlock c i ↔ v ∈ Set.range (c.emb i) := by
  simp [orderedFinpartitionBlock]

@[simp]
theorem card_orderedFinpartitionBlock {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    (orderedFinpartitionBlock c i).card = c.partSize i := by
  simp [orderedFinpartitionBlock]

theorem orderedFinpartitionBlock_nonempty {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    (orderedFinpartitionBlock c i).Nonempty := by
  let z : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
  exact ⟨c.emb i z, by simp [orderedFinpartitionBlock]⟩

theorem orderedFinpartitionBlock_injective {n : ℕ}
    (c : OrderedFinpartition n) :
    Function.Injective (orderedFinpartitionBlock c) := by
  intro i j hij
  by_contra hne
  let z : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
  have hz : c.emb i z ∈ orderedFinpartitionBlock c i := by
    simp [orderedFinpartitionBlock]
  have hzj : c.emb i z ∈ orderedFinpartitionBlock c j := by
    rw [← hij]
    exact hz
  have hdis := c.disjoint (Set.mem_univ i) (Set.mem_univ j) hne
  exact (Set.disjoint_left.1 hdis)
    ((mem_orderedFinpartitionBlock c i _).mp hz)
    ((mem_orderedFinpartitionBlock c j _).mp hzj)

/-- Forget the canonical ordering and increasing block parameterizations. -/
def orderedFinpartitionToFinpartition {n : ℕ}
    (c : OrderedFinpartition n) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  classical
  let parts : Finset (Finset (Fin n)) :=
    Finset.univ.image (orderedFinpartitionBlock c)
  refine Finpartition.ofExistsUnique parts (fun _ _ _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro v _
    obtain ⟨i, a, hia⟩ := c.cover v
    refine ⟨orderedFinpartitionBlock c i, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · exact (mem_orderedFinpartitionBlock c i v).mpr ⟨a, hia⟩
    · intro b hb
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hb.1
      apply congrArg (orderedFinpartitionBlock c)
      by_contra hne
      have hdis := c.disjoint (Set.mem_univ i) (Set.mem_univ j)
        (fun h ↦ hne h.symm)
      exact (Set.disjoint_left.1 hdis)
        ((mem_orderedFinpartitionBlock c i v).mp
          ((mem_orderedFinpartitionBlock c i v).mpr ⟨a, hia⟩))
        ((mem_orderedFinpartitionBlock c j v).mp hb.2)
  · intro hempty
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hempty
    exact (orderedFinpartitionBlock_nonempty c i).ne_empty hi

@[simp]
theorem parts_orderedFinpartitionToFinpartition {n : ℕ}
    (c : OrderedFinpartition n) :
    (orderedFinpartitionToFinpartition c).parts =
      Finset.univ.image (orderedFinpartitionBlock c) :=
  rfl

@[simp]
theorem card_parts_orderedFinpartitionToFinpartition {n : ℕ}
    (c : OrderedFinpartition n) :
    (orderedFinpartitionToFinpartition c).parts.card = c.length := by
  rw [parts_orderedFinpartitionToFinpartition,
    Finset.card_image_of_injective _ (orderedFinpartitionBlock_injective c)]
  simp

/-- The largest vertex of a nonempty part of a finite partition. -/
def finpartitionPartMax {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n)))
    (b : Q.parts) : Fin n :=
  b.1.max' (Q.nonempty_of_mem_parts b.2)

theorem finpartitionPartMax_mem {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n)))
    (b : Q.parts) : finpartitionPartMax Q b ∈ b.1 :=
  Finset.max'_mem _ _

theorem finpartitionPartMax_injective {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (finpartitionPartMax Q) := by
  intro b d hbd
  apply Subtype.ext
  exact Q.eq_of_mem_parts b.2 d.2 (finpartitionPartMax_mem Q b)
    (hbd ▸ finpartitionPartMax_mem Q d)

@[reducible]
noncomputable def finpartitionPartMaxLinearOrder {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n))) :
    LinearOrder Q.parts :=
  LinearOrder.lift' (finpartitionPartMax Q)
    (finpartitionPartMax_injective Q)

/-- Increasing enumeration of partition parts by their largest vertex. -/
noncomputable def orderedFinpartitionPartEquiv {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n))) :
    Fin Q.parts.card ≃ Q.parts := by
  letI : LinearOrder Q.parts := finpartitionPartMaxLinearOrder Q
  exact (Fintype.orderIsoFinOfCardEq Q.parts (Fintype.card_coe _)).toEquiv

set_option maxHeartbeats 800000 in
-- Elaborating the dependent block embeddings and their disjointness proof is
-- substantially more expensive than checking the resulting declaration.
/-- Put the canonical order and increasing parameterizations on an ordinary
finite partition. -/
noncomputable def finpartitionToOrderedFinpartition {n : ℕ}
    (Q : Finpartition (Finset.univ : Finset (Fin n))) :
    OrderedFinpartition n where
  length := Q.parts.card
  partSize i := (orderedFinpartitionPartEquiv Q i).1.card
  partSize_pos i := (Q.nonempty_of_mem_parts
    (orderedFinpartitionPartEquiv Q i).2).card_pos
  emb i := ((orderedFinpartitionPartEquiv Q i).1.orderEmbOfFin rfl)
  emb_strictMono i :=
    ((orderedFinpartitionPartEquiv Q i).1.orderEmbOfFin rfl).strictMono
  parts_strictMono := by
    intro i j hij
    change
      ((orderedFinpartitionPartEquiv Q i).1.orderEmbOfFin rfl)
          ⟨(orderedFinpartitionPartEquiv Q i).1.card - 1,
            Nat.sub_one_lt_of_lt (Q.nonempty_of_mem_parts
              (orderedFinpartitionPartEquiv Q i).2).card_pos⟩ <
        ((orderedFinpartitionPartEquiv Q j).1.orderEmbOfFin rfl)
          ⟨(orderedFinpartitionPartEquiv Q j).1.card - 1,
            Nat.sub_one_lt_of_lt (Q.nonempty_of_mem_parts
              (orderedFinpartitionPartEquiv Q j).2).card_pos⟩
    rw [Finset.orderEmbOfFin_last rfl
      (Q.nonempty_of_mem_parts
        (orderedFinpartitionPartEquiv Q i).2).card_pos]
    rw [Finset.orderEmbOfFin_last rfl
      (Q.nonempty_of_mem_parts
        (orderedFinpartitionPartEquiv Q j).2).card_pos]
    letI : LinearOrder Q.parts := finpartitionPartMaxLinearOrder Q
    change finpartitionPartMax Q (orderedFinpartitionPartEquiv Q i) <
      finpartitionPartMax Q (orderedFinpartitionPartEquiv Q j)
    let e := @Fintype.orderIsoFinOfCardEq Q.parts
      (finpartitionPartMaxLinearOrder Q) inferInstance Q.parts.card
      (Fintype.card_coe _)
    have hpart0 := (@OrderIso.strictMono (Fin Q.parts.card) Q.parts
      inferInstance (finpartitionPartMaxLinearOrder Q).toPreorder e) hij
    change finpartitionPartMax Q (e i) <
      finpartitionPartMax Q (e j) at hpart0
    simpa only [orderedFinpartitionPartEquiv, e] using hpart0
  disjoint := by
    intro i _hi j _hj hij
    change Disjoint
      (Set.range (((orderedFinpartitionPartEquiv Q i).1.orderEmbOfFin rfl) :
        Fin (orderedFinpartitionPartEquiv Q i).1.card → Fin n))
      (Set.range (((orderedFinpartitionPartEquiv Q j).1.orderEmbOfFin rfl) :
        Fin (orderedFinpartitionPartEquiv Q j).1.card → Fin n))
    rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin]
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hneVal : (orderedFinpartitionPartEquiv Q i).1 ≠
        (orderedFinpartitionPartEquiv Q j).1 := by
      intro hval
      apply hij
      exact (orderedFinpartitionPartEquiv Q).injective (Subtype.ext hval)
    exact (Finset.disjoint_left.mp (Q.disjoint
      (orderedFinpartitionPartEquiv Q i).2
      (orderedFinpartitionPartEquiv Q j).2 hneVal)) hvi hvj
  cover v := by
    obtain ⟨b, hb, hvb⟩ := Q.exists_mem (Finset.mem_univ v)
    let i : Fin Q.parts.card :=
      (orderedFinpartitionPartEquiv Q).symm ⟨b, hb⟩
    refine ⟨i, ?_⟩
    rw [Finset.range_orderEmbOfFin]
    simpa [i] using hvb

theorem orderedFinpartitionBlock_finpartitionToOrderedFinpartition
    {n : ℕ} (Q : Finpartition (Finset.univ : Finset (Fin n)))
    (i : Fin (finpartitionToOrderedFinpartition Q).length) :
    orderedFinpartitionBlock (finpartitionToOrderedFinpartition Q) i =
      (orderedFinpartitionPartEquiv Q i).1 := by
  classical
  ext v
  rw [mem_orderedFinpartitionBlock]
  change v ∈ Set.range
      (((orderedFinpartitionPartEquiv Q i).1.orderEmbOfFin rfl) :
        Fin (orderedFinpartitionPartEquiv Q i).1.card → Fin n) ↔ _
  rw [Finset.range_orderEmbOfFin]
  rfl

theorem orderedFinpartitionToFinpartition_finpartitionToOrderedFinpartition
    {n : ℕ} (Q : Finpartition (Finset.univ : Finset (Fin n))) :
    orderedFinpartitionToFinpartition
        (finpartitionToOrderedFinpartition Q) = Q := by
  classical
  apply Finpartition.ext
  rw [parts_orderedFinpartitionToFinpartition]
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [orderedFinpartitionBlock_finpartitionToOrderedFinpartition]
    exact (orderedFinpartitionPartEquiv Q i).2
  · intro hb
    let i := (orderedFinpartitionPartEquiv Q).symm ⟨b, hb⟩
    refine ⟨i, ?_⟩
    rw [orderedFinpartitionBlock_finpartitionToOrderedFinpartition]
    simpa [i]

private theorem orderedFinpartitionBlock_max {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    (orderedFinpartitionBlock c i).max'
        (orderedFinpartitionBlock_nonempty c i) =
      c.emb i ⟨c.partSize i - 1,
        Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩ := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · simp [orderedFinpartitionBlock]
  · intro v hv
    obtain ⟨a, rfl⟩ := (mem_orderedFinpartitionBlock c i v).mp hv
    apply (c.emb_strictMono i).monotone
    exact Fin.mk_le_mk.mpr (by omega)

private theorem orderedFinpartitionBlock_last_eq_of_eq {n : ℕ}
    {c d : OrderedFinpartition n} {i : Fin c.length} {j : Fin d.length}
    (hblock : orderedFinpartitionBlock c i =
      orderedFinpartitionBlock d j) :
    c.emb i ⟨c.partSize i - 1,
        Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩ =
      d.emb j ⟨d.partSize j - 1,
        Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩ := by
  apply le_antisymm
  · have hmem : c.emb i
        ⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩ ∈
        orderedFinpartitionBlock d j := by
      rw [← hblock]
      exact (mem_orderedFinpartitionBlock c i _).mpr
        ⟨⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩, rfl⟩
    obtain ⟨a, ha⟩ := (mem_orderedFinpartitionBlock d j _).mp hmem
    rw [← ha]
    apply (d.emb_strictMono j).monotone
    exact Fin.mk_le_mk.mpr (by omega)
  · have hmem : d.emb j
        ⟨d.partSize j - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩ ∈
        orderedFinpartitionBlock c i := by
      rw [hblock]
      exact (mem_orderedFinpartitionBlock d j _).mpr
        ⟨⟨d.partSize j - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩, rfl⟩
    obtain ⟨a, ha⟩ := (mem_orderedFinpartitionBlock c i _).mp hmem
    rw [← ha]
    apply (c.emb_strictMono i).monotone
    exact Fin.mk_le_mk.mpr (by omega)

theorem orderedFinpartitionToFinpartition_injective {n : ℕ} :
    Function.Injective
      (orderedFinpartitionToFinpartition (n := n)) := by
  intro c d hcd
  have hparts : Finset.univ.image (orderedFinpartitionBlock c) =
      Finset.univ.image (orderedFinpartitionBlock d) := by
    simpa using congrArg Finpartition.parts hcd
  have hlength : c.length = d.length := by
    have := congrArg Finset.card hparts
    simpa [Finset.card_image_of_injective _
      (orderedFinpartitionBlock_injective c),
      Finset.card_image_of_injective _
      (orderedFinpartitionBlock_injective d)] using this
  have hmaxRange :
      Set.range (fun i : Fin c.length ↦
        c.emb i ⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩) =
      Set.range (fun i : Fin c.length ↦
        let j := Fin.cast hlength i
        d.emb j ⟨d.partSize j - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have hmem : orderedFinpartitionBlock c i ∈
          Finset.univ.image (orderedFinpartitionBlock d) := by
        rw [← hparts]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      obtain ⟨j, _hj, hj⟩ := Finset.mem_image.mp hmem
      refine ⟨Fin.cast hlength.symm j, ?_⟩
      change d.emb (Fin.cast hlength (Fin.cast hlength.symm j))
          ⟨d.partSize (Fin.cast hlength (Fin.cast hlength.symm j)) - 1,
            Nat.sub_one_lt_of_lt (d.partSize_pos _)⟩ =
        c.emb i ⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
      have hjcast : Fin.cast hlength (Fin.cast hlength.symm j) = j := by
        apply Fin.eq_of_val_eq
        rfl
      rw [hjcast]
      exact orderedFinpartitionBlock_last_eq_of_eq hj
    · rintro ⟨j, rfl⟩
      let j' := Fin.cast hlength j
      have hmem : orderedFinpartitionBlock d j' ∈
          Finset.univ.image (orderedFinpartitionBlock c) := by
        rw [hparts]
        exact Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩
      obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
      refine ⟨i, ?_⟩
      change c.emb i ⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩ =
        d.emb j' ⟨d.partSize j' - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j')⟩
      exact orderedFinpartitionBlock_last_eq_of_eq hi
  have hmax :
      (fun i : Fin c.length ↦
        c.emb i ⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩) =
      (fun i : Fin c.length ↦
        let j := Fin.cast hlength i
        d.emb j ⟨d.partSize j - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩) :=
    ((c.parts_strictMono.range_inj
      (d.parts_strictMono.comp (Fin.cast_strictMono hlength))).mp hmaxRange)
  have hblock : ∀ i : Fin c.length,
      orderedFinpartitionBlock c i =
        orderedFinpartitionBlock d (Fin.cast hlength i) := by
    intro i
    have hcMem : orderedFinpartitionBlock c i ∈
        (orderedFinpartitionToFinpartition d).parts := by
      rw [parts_orderedFinpartitionToFinpartition, ← hparts]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hdMem : orderedFinpartitionBlock d (Fin.cast hlength i) ∈
        (orderedFinpartitionToFinpartition d).parts := by
      let j := Fin.cast hlength i
      change orderedFinpartitionBlock d j ∈ _
      rw [parts_orderedFinpartitionToFinpartition]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    let vmax := c.emb i ⟨c.partSize i - 1,
      Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
    let j := Fin.cast hlength i
    change orderedFinpartitionBlock c i = orderedFinpartitionBlock d j
    apply (orderedFinpartitionToFinpartition d).eq_of_mem_parts
      (a := vmax) hcMem hdMem
    · exact (mem_orderedFinpartitionBlock c i _).mpr
        ⟨⟨c.partSize i - 1,
          Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩, rfl⟩
    · have hvEq : vmax = d.emb j
          ⟨d.partSize j - 1,
            Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩ :=
        congrFun hmax i
      rw [hvEq]
      exact (mem_orderedFinpartitionBlock d j _).mpr
        ⟨⟨d.partSize j - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos j)⟩, rfl⟩
  have hpartSize (i : Fin c.length) :
      c.partSize i = d.partSize (Fin.cast hlength i) := by
    rw [← card_orderedFinpartitionBlock c i,
      ← card_orderedFinpartitionBlock d (Fin.cast hlength i), hblock i]
  apply OrderedFinpartition.ext hlength
  · exact (Fin.heq_fun_iff hlength).mpr hpartSize
  · refine Function.hfunext (congrArg Fin hlength) ?_
    intro i i' hi'
    have hival : (i' : ℕ) = (i : ℕ) :=
      Fin.val_eq_val_of_heq hi'.symm
    have hiEq : i' = Fin.cast hlength i :=
      Fin.eq_of_val_eq hival
    subst hiEq
    refine (Fin.heq_fun_iff (hpartSize i)).mpr ?_
    intro a
    let j := Fin.cast hlength i
    let hsize := hpartSize i
    have hfun : c.emb i =
        (fun a : Fin (c.partSize i) ↦ d.emb j (Fin.cast hsize a)) := by
      apply (c.emb_strictMono i).range_inj
          ((d.emb_strictMono j).comp (Fin.cast_strictMono hsize)) |>.mp
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        have hv : c.emb i a ∈ orderedFinpartitionBlock c i :=
          (mem_orderedFinpartitionBlock c i _).mpr ⟨a, rfl⟩
        rw [hblock i] at hv
        obtain ⟨b, hb⟩ :=
          (mem_orderedFinpartitionBlock d j _).mp hv
        refine ⟨Fin.cast hsize.symm b, ?_⟩
        simpa [j, hsize] using hb
      · rintro ⟨a, rfl⟩
        apply (mem_orderedFinpartitionBlock c i _).mp
        rw [hblock i]
        exact (mem_orderedFinpartitionBlock d j _).mpr
          ⟨Fin.cast hsize a, rfl⟩
    exact congrFun hfun a

/-- Canonical equivalence between the ordered partitions in Faà di Bruno
and ordinary finite set partitions. -/
noncomputable def orderedFinpartitionEquivFinpartition (n : ℕ) :
    OrderedFinpartition n ≃
      Finpartition (Finset.univ : Finset (Fin n)) :=
  Equiv.ofBijective orderedFinpartitionToFinpartition
    ⟨orderedFinpartitionToFinpartition_injective,
      fun Q ↦ ⟨finpartitionToOrderedFinpartition Q,
        orderedFinpartitionToFinpartition_finpartitionToOrderedFinpartition Q⟩⟩

/-- An equivalence of finite carrier types induces an order isomorphism of
their finset lattices. -/
noncomputable def finsetOrderIsoOfEquiv {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Finset ι ≃o Finset κ where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp [Equiv.finsetCongr_apply]

/-- Transport an ordinary finite partition across an equivalence of its
labelled carrier type. -/
noncomputable def finpartitionCongr {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) :
    Finpartition (Finset.univ : Finset ι) ≃
      Finpartition (Finset.univ : Finset κ) where
  toFun P := (P.map (finsetOrderIsoOfEquiv e)).copy (by
    simp [finsetOrderIsoOfEquiv])
  invFun P := (P.map (finsetOrderIsoOfEquiv e.symm)).copy (by
    simp [finsetOrderIsoOfEquiv])
  left_inv P := by
    apply Finpartition.ext
    ext s
    simp [finsetOrderIsoOfEquiv, Equiv.finsetCongr_apply,
      Finset.map_map]
  right_inv P := by
    apply Finpartition.ext
    ext s
    simp [finsetOrderIsoOfEquiv, Equiv.finsetCongr_apply,
      Finset.map_map]

/-- Ordered partitions parameterize partitions of every labelled finite
type, after choosing its canonical `Fin` enumeration. -/
noncomputable def orderedFinpartitionEquivFinpartitionOfFintype
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    OrderedFinpartition (Fintype.card ι) ≃
      Finpartition (Finset.univ : Finset ι) :=
  (orderedFinpartitionEquivFinpartition (Fintype.card ι)).trans
    (finpartitionCongr (Fintype.equivFin ι).symm)

@[simp]
theorem card_parts_orderedFinpartitionEquivFinpartitionOfFintype
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (c : OrderedFinpartition (Fintype.card ι)) :
    ((orderedFinpartitionEquivFinpartitionOfFintype ι) c).parts.card =
      c.length := by
  simpa [orderedFinpartitionEquivFinpartitionOfFintype, finpartitionCongr]
    using card_parts_orderedFinpartitionToFinpartition c

end

end YangMills.Polymer
