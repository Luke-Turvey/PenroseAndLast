/-
Copyright (c) 2026 Luke Turvey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Turvey
-/
module

public import Mathlib

/-!
# Counting Measures

This file contains the definitions and elementary properties of
finite and countable counting measures,
following Lectures on the Poisson Process (2017) by Gunter Last
 and Matthew Penrose.

It further contains instance which defines the inherited measurable space
of the space of counting measures from the space of all measures
-/

public section

namespace PenroseAndLast

open MeasureTheory
open scoped ENNReal

/-- A finite counting measure is a measure taking natural number values
on every measurable set. It is an element of N_<∞(X) -/
def IsFiniteCountingMeasure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∀ B : Set X, MeasurableSet B → ∃ n : ℕ, μ B = (n : ENNReal)


theorem IsFiniteCountingMeasure.zero
    {X : Type*} [MeasurableSpace X] :
    IsFiniteCountingMeasure (0 : Measure X) := by
    intro B hB
    use 0
    simp

theorem IsFiniteCountingMeasure.dirac
    {X : Type*} [MeasurableSpace X] (x : X) :
    IsFiniteCountingMeasure (Measure.dirac x) := by
    intro B hB
    have h := Measure.dirac_apply_eq_zero_or_one (s := B) ( a:= x)
    rcases h with h0 | h1
    · use 0
      simp [h0]
    · use 1
      simp [h1]

theorem IsFiniteCountingMeasure.add
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X)
    (hμ : IsFiniteCountingMeasure μ)
    (hν : IsFiniteCountingMeasure ν) :
    IsFiniteCountingMeasure (μ + ν) := by
  intro B hB
  obtain ⟨μn, hμn⟩ := hμ B hB
  obtain ⟨νn, hνn⟩ := hν B hB
  use μn + νn
  simp [hμn,hνn]

/-- A counting measure is a measure that can be expressed as a countable
sum of finite counting measures. It is an element of N(X). -/
def IsCountingMeasure
  {X : Type*} [MeasurableSpace X]
  (μ : Measure X) : Prop :=
  ∃ (α : ℕ → Measure X) , (∀ i : ℕ, IsFiniteCountingMeasure (α i))
  ∧ μ = Measure.sum α

@[expose]
def CountingMeasure
    (X : Type*) [MeasurableSpace X] :=
  { μ : Measure X // IsCountingMeasure μ}


/-- Every finite counting measure is a counting measure.
N_<∞(X) ⊆ N(X) -/
theorem IsCountingMeasure.of_isFiniteCountingMeasure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (hμ : IsFiniteCountingMeasure μ) :
    IsCountingMeasure μ := by
  use (fun n => if n= 0 then μ else 0)
  constructor
  · intro i
    by_cases hi : i=0
    · simp [hi, hμ]
    · simp[hi, IsFiniteCountingMeasure.zero]
  · apply Measure.ext
    intro s hs
    simp only [Measure.sum_apply  (fun n => if n= 0 then μ else 0) hs]
    have h (i : ℕ) : (if i = 0 then μ else 0) s
        = (if i = 0 then μ s else 0) := by
      split_ifs
      · simp
      · simp
    simp_rw[h]
    rw [tsum_ite_eq (0 : ℕ ) (fun _ => μ s)]

theorem IsCountingMeasure.zero
    {X : Type*} [MeasurableSpace X] :
    IsCountingMeasure (0 : Measure X) := by
  exact IsCountingMeasure.of_isFiniteCountingMeasure 0 IsFiniteCountingMeasure.zero

theorem IsCountingMeasure.dirac
    {X : Type*} [MeasurableSpace X] (x : X) :
    IsCountingMeasure (Measure.dirac x) := by
  exact IsCountingMeasure.of_isFiniteCountingMeasure
    (Measure.dirac x) (IsFiniteCountingMeasure.dirac x)

/-- Define the dirac measure as a subtype of CountingMeasure -/
@[expose]
noncomputable def CountingMeasure.dirac
    {X : Type*} [MeasurableSpace X]
    (x : X) :
    CountingMeasure X  :=
    ⟨Measure.dirac x, IsCountingMeasure.dirac x⟩


theorem IsCountingMeasure.add
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X)
    (hμ : IsCountingMeasure μ)
    (hν : IsCountingMeasure ν) :
    IsCountingMeasure (μ + ν) := by
  obtain ⟨μs, hμs⟩ := hμ
  obtain ⟨νs, hνs⟩ := hν
  use μs + νs
  constructor
  · intro i
    have h : (μs + νs) i = μs i + νs i := by exact Pi.add_apply μs νs i
    rw[h]
    exact IsFiniteCountingMeasure.add (μs i) (νs i) (hμs.1 i) (hνs.1 i)
  · simp_rw [hμs.2, hνs.2, Measure.sum_add_sum μs νs]
    apply Measure.sum_congr
    simp

/-- Instance of Add for CountingMeasure X -/
instance {X : Type*} [MeasurableSpace X] :
    Add (CountingMeasure X) where
  add μ ν :=
    ⟨μ.val + ν.val,
      IsCountingMeasure.add μ.val ν.val μ.property ν.property⟩


/-- For f: ℕ → ℕ we have ∑_i ∈ ℕ, f(i) ∈ ℕ ∪ {∞}. -/
theorem tsum_nat_eq_nat_or_inf
  (f : ℕ → ℕ) :
  (∃ n : ℕ , ∑' i : ℕ, (f i : ENNReal) = n)
    ∨ (∑' i : ℕ, (f i : ENNReal) = ∞) := by
  by_cases htop : (∑' i : ℕ, (f i : ENNReal) = ∞)
  · right
    exact htop
  · left
    have hfinite :
        {i : ℕ | (1 : ENNReal) ≤ (f i : ENNReal)}.Finite := by
      apply ENNReal.finite_const_le_of_tsum_ne_top htop
      simp
    let s := hfinite.toFinset
    have hzero : ∀ i : ℕ, i ∉ s → (f i : ENNReal) = 0 := by
      intro i hi
      have hfi : f i = 0 := by
        by_contra hne
        have h1e : (1 : ENNReal) ≤ (f i : ENNReal) := by
          exact_mod_cast (Nat.one_le_cast_iff_ne_zero.mpr hne)
        exact hi ( hfinite.mem_toFinset.mpr h1e)
      exact_mod_cast hfi
    refine ⟨∑ i ∈ s, f i, ?_⟩
    rw[tsum_eq_sum hzero]
    exact (Nat.cast_sum s f).symm


/-- ∀ μ ∈ N(X) ∀ B ∈ χ, μ(B) ∈ ℕ₀ ∪ {∞} -/
theorem CountingMeasure.apply_eq_nat_or_inf
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (hμ : IsCountingMeasure μ)
    (B : Set X)
    (hB : MeasurableSet B) :
    (∃ n : ℕ, μ B = (n : ENNReal)) ∨ (μ B = ∞) := by
  obtain ⟨ι, ⟨hfinite,hsum⟩⟩ := hμ
  have hBsum : μ B = ∑' i : ℕ, (ι i) B := by
    rw [hsum, Measure.sum_apply ι hB]
  have hμifinite :  ∀ i : ℕ, ∃ ni : ℕ, (ι i) B = (ni : ENNReal) := by
    intro i
    obtain ⟨ni, hni⟩ := hfinite i B hB
    use ni
  choose f hf using hμifinite
  simp_rw [hf] at hBsum
  rcases (tsum_nat_eq_nat_or_inf f) with h₁ | h₂
  · left
    obtain ⟨n, hn⟩ := h₁
    use n
    rw[hBsum,hn]
  · right
    rw [hBsum,h₂]


/-- For a measurable space (X,χ). Let the measurable space (N(X),𝓝(X))
be the restriction of the measurable space of all measures on X
(M(X),\MM(X)) to N(X). -/
instance {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (CountingMeasure X) :=
  inferInstanceAs
    (MeasurableSpace
      { μ : Measure X // IsCountingMeasure μ})




end PenroseAndLast
