/-
Copyright (c) 2026 Luke Turvey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Turvey
-/
module

public import Mathlib

/-!
# Point Processes

This file develops the basic theory of point processes,
following Chapter 2 Lectures on the Poisson Process (2017)
by Gunter Last and Matthew Penrose,
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


theorem isFiniteCountingMeasure_zero
    {X : Type*} [MeasurableSpace X] :
    IsFiniteCountingMeasure (0 : Measure X) := by
    intro B hB
    use 0
    simp

theorem isFiniteCountingMeasure_dirac
    {X : Type*} [MeasurableSpace X] (x : X) :
    IsFiniteCountingMeasure (Measure.dirac x) := by
    intro B hB
    have h := Measure.dirac_apply_eq_zero_or_one (s := B) ( a:= x)
    rcases h with h0 | h1
    · use 0
      simp [h0]
    · use 1
      simp [h1]

theorem isFiniteCountingMeasure_add
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
theorem isCountingMeasure_of_isFiniteCountingMeasure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (hμ : IsFiniteCountingMeasure μ) :
    IsCountingMeasure μ := by
  use (fun n => if n= 0 then μ else 0)
  constructor
  · intro i
    by_cases hi : i=0
    · simp [hi, hμ]
    · simp[hi, isFiniteCountingMeasure_zero]
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

theorem isCountingMeasure_zero
    {X : Type*} [MeasurableSpace X] :
    IsCountingMeasure (0 : Measure X) := by
  exact isCountingMeasure_of_isFiniteCountingMeasure 0 isFiniteCountingMeasure_zero

theorem isCountingMeasure_dirac
    {X : Type*} [MeasurableSpace X] (x : X) :
    IsCountingMeasure (Measure.dirac x) := by
  exact isCountingMeasure_of_isFiniteCountingMeasure
    (Measure.dirac x) (isFiniteCountingMeasure_dirac x)

theorem isCountingMeasure_add
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
    exact isFiniteCountingMeasure_add (μs i) (νs i) (hμs.1 i) (hνs.1 i)
  · simp_rw [hμs.2, hνs.2, Measure.sum_add_sum μs νs]
    apply Measure.sum_congr
    simp


/-- For a measurable space (X,χ). Let the measurable space (N(X),𝓝(X))
be the restriction of the measurable space of all measures on X
(M(X),\MM(X)) to N(X). -/
instance {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (CountingMeasure X) :=
  inferInstanceAs
    (MeasurableSpace
      { μ : Measure X // IsCountingMeasure μ})


/-- ∀ B ∈ χ, the function e_B : N(X) → [0,∞] that maps
μ to μ(B) is measurable w.r.t. 𝓝(X) -/
theorem countingMeasureEvaluationMapisMeasurable
    {X : Type*} [MeasurableSpace X]
    (B : Set X)
    (hB : MeasurableSet B) :
    Measurable (fun μ : CountingMeasure X => μ.val B) := by
  have h₁ : Measurable (fun μ : Measure X => μ B)
    := Measure.measurable_coe hB
  have h₂ : Measurable (fun μ : CountingMeasure X => μ.val)
    := measurable_subtype_coe
  exact Measurable.comp h₁ h₂

/-- Define the generating sets {μ ∈ N(X) : μ(B)= k for some k ∈ ℕ} -/
def generatingSets
    (X : Type*) [MeasurableSpace X] :
    Set (Set (CountingMeasure X)) :=
  {E | ∃ (B : Set X) (k : ℕ),
    MeasurableSet B ∧ E = {μ : CountingMeasure X | μ.val B = (k : ENNReal)}}

/-- The sets {μ ∈ N(X) : μ(B) = k} ∀ B ∈ χ, k ∈ ℕ₀
 are measurable w.r.t 𝓝(X). -/
theorem countingMeasureSingletonMeasurableSet
    {X : Type*} [MeasurableSpace X] :
    ∀ B ∈ (generatingSets X), MeasurableSet B := by
  intro E hE
  rcases hE with ⟨B, k, hB, hEdef⟩
  rw [hEdef]
  have hₖ : MeasurableSet ({(k : ENNReal)} : Set ENNReal) := by
    exact MeasurableSet.singleton (k : ENNReal)
  apply MeasurableSet.preimage hₖ
    (countingMeasureEvaluationMapisMeasurable B hB)


/-- For f: ℕ → ℕ we have ∑_i ∈ ℕ, f(i) ∈ ℕ ∪ {∞}. -/
theorem tsum_nat_eq_nat_or_top
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
theorem CountingMeasureIsENat
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
  rcases (tsum_nat_eq_nat_or_top f) with h₁ | h₂
  · left
    obtain ⟨n, hn⟩ := h₁
    use n
    rw[hBsum,hn]
  · right
    rw [hBsum,h₂]


/-- σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) ⊆ 𝓝(X) -/
theorem generatedSigmaAlgebraInRestrictedSigmaAlgebra
    (X : Type*) [MeasurableSpace X] :
    MeasurableSpace.generateFrom (generatingSets X) ≤
      (inferInstance : MeasurableSpace (CountingMeasure X)) := by
  apply MeasurableSpace.generateFrom_le
  intro B hB
  apply countingMeasureSingletonMeasurableSet
  exact hB





/-- ∀ B ∈ χ, ∀ k ∈ ℕ
{μ ∈ N(X) : μ(B) = k} ∈  σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem generatingSetsAreMeasurable
    {X : Type*} [MeasurableSpace X]
    (B : Set X)
    (hB : MeasurableSet B)
    (k : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
     ({μ : CountingMeasure X | μ.val B = (k : ENNReal)}
      : Set  (CountingMeasure X)) := by
  apply MeasurableSpace.measurableSet_generateFrom
  refine ⟨B, k, hB, ?_⟩
  rfl

/-- ∀ B ∈ χ,
{μ ∈ N(X) : μ(B) = ∞} ∈  σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem infiniteMapSetIsMeasurable
    {X : Type*} [MeasurableSpace X]
    (B : Set X)
    (hB : MeasurableSet B) :
    MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
     ({μ : CountingMeasure X | μ.val B = ∞}
      : Set  (CountingMeasure X)) := by
  let h : MeasurableSpace (CountingMeasure X) :=
    MeasurableSpace.generateFrom (generatingSets X)
  have h₁ : ({μ : CountingMeasure X | μ.val B = ∞}
        : Set  (CountingMeasure X))
      = (⋃ k : ℕ, ({μ : CountingMeasure X | μ.val B = (k : ENNReal)}
        : Set  (CountingMeasure X)))ᶜ := by
    refine Set.ext ?_
    intro ν
    constructor
    · intro hν
      change ν.val B = ∞ at hν
      simp only [
        Set.mem_compl_iff,
        Set.mem_iUnion,
        Set.mem_ofPred_eq,
        not_exists
      ]
      intro x
      rw[hν]
      simp
    · intro hν₂
      change ν.val B = ∞
      simp only [
        Set.mem_compl_iff,
        Set.mem_iUnion,
        Set.mem_ofPred_eq,
        not_exists
      ] at hν₂
      rcases CountingMeasureIsENat ν.val ν.property B hB with
        ⟨k, hk ⟩ | htop
      · exact (hν₂ k hk).elim
      · exact htop
  have h₂ : MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
      (⋃ k : ℕ, ({μ : CountingMeasure X | μ.val B = (k : ENNReal)}
        : Set  (CountingMeasure X))) := by
    apply MeasurableSet.iUnion
    intro k
    exact generatingSetsAreMeasurable B hB k
  rw[h₁]
  exact h₂.compl

/-- ∀ D ⊆ [0,∞], ∞ ∉ D, ∀ B ∈ χ,
{μ ∈ N(X) : μ(B) ∈ D} ∈ σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem mapSetsAreMeasurable_when_inf_not_mem
    {X : Type*} [MeasurableSpace X]
    (D : Set ENNReal)
    (hD : (∞ : ENNReal) ∉ D)
    (B : Set X)
    (hB : MeasurableSet B) :
    MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
      ({μ : CountingMeasure X | μ.val B ∈ D}
        : Set  (CountingMeasure X)) := by
  let indices : Set ℕ := {k | (k : ENNReal) ∈ D}
  have h : ({μ : CountingMeasure X | μ.val B ∈ D}
      : Set  (CountingMeasure X)) =
      (⋃ k ∈ indices, ({μ : CountingMeasure X | μ.val B = (k : ENNReal)}
      : Set  (CountingMeasure X))) :=
    calc
      ({μ : CountingMeasure X | μ.val B ∈ D}
        : Set  (CountingMeasure X)) =
        ({μ : CountingMeasure X | μ.val B ∈ D ∧ μ.val B ≠ (∞ : ENNReal)}
        : Set  (CountingMeasure X)) := by
          apply Set.ext
          intro ν
          constructor
          · intro hν₁
            refine Set.mem_ofPred.mpr ?_
            refine ⟨hν₁, ?_⟩
            intro heq
            change (ν.val B ∈ D) at hν₁
            rw[heq] at hν₁
            contradiction
          · intro hν₂
            change (ν.val B ∈ D ∧ ν.val B ≠ ∞) at hν₂
            change ν.val B ∈ D
            exact hν₂.1
      _ = (⋃ k ∈ indices , ({μ : CountingMeasure X | μ.val B = (k : ENNReal)}
        : Set  (CountingMeasure X))) := by
        apply Set.ext
        intro ν
        constructor
        · intro hν₁
          change (ν.val B ∈ D ∧ ν.val B ≠ ∞) at hν₁
          apply Set.mem_iUnion.mpr
          rcases CountingMeasureIsENat ν.val ν.property B hB with
            ⟨k,hk⟩ | hinf
          · use k
            rw[hk] at hν₁
            apply Set.mem_iUnion.mpr
            have hkindices : k ∈ indices := by exact hν₁.1
            use hkindices
            exact hk
          · by_contra
            exact hν₁.2 hinf
        · intro hν₂
          refine Set.mem_ofPred.mpr ?_
          simp only [Set.mem_iUnion] at hν₂
          obtain ⟨k,⟨hk,hνk⟩⟩ := hν₂
          change ν.val B = (k : ENNReal) at hνk
          change (k : ENNReal) ∈ D at hk
          rw[←hνk] at hk
          refine ⟨hk,?_⟩
          rw[hνk]
          simp
  rw[h]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro k
  apply generatingSetsAreMeasurable
  exact hB

/-- ∀ D ⊆ [0,∞] ∀ B ∈ χ,
 {μ ∈ N(X) : μ(B) ∈ D} ∈ σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem mapSetsAreMeasurable
    {X : Type*} [MeasurableSpace X]
    (D : Set ENNReal)
    (B : Set X)
    (hB : MeasurableSet B) :
    MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
      ({μ : CountingMeasure X | μ.val B ∈ D}
        : Set  (CountingMeasure X)) := by
  by_cases hinf : (∞ : ENNReal) ∉ D
  · exact mapSetsAreMeasurable_when_inf_not_mem D hinf B hB
  · have h₂ : MeasurableSet[MeasurableSpace.generateFrom (generatingSets X)]
      ({μ : CountingMeasure X | μ.val B ∈ Dᶜ}
        : Set  (CountingMeasure X)) :=  by
      exact mapSetsAreMeasurable_when_inf_not_mem Dᶜ hinf B hB
    have h₃ :
      ({μ : CountingMeasure X | μ.val B ∈ Dᶜ}
        : Set  (CountingMeasure X)) =
      ({μ : CountingMeasure X | μ.val B ∈ D}ᶜ
        : Set  (CountingMeasure X)) := by
        apply Set.ext
        intro ν
        constructor
        · intro hν
          exact hν
        · intro hν
          exact hν
    rw [h₃] at h₂
    exact h₂.of_compl

/-- ∀ B ∈ χ, e_B : (N(X), σ  ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }))
                    → ([0,∞], Borel([0,∞]))
    e_B(μ) := μ(B) is measurable -/
theorem evaluationMapIsGeneratedMeasurable
    {X : Type*} [ MeasurableSpace X]
    (B : Set X)
    (hB : MeasurableSet B) :
    Measurable[MeasurableSpace.generateFrom (generatingSets X)]
      (fun μ : CountingMeasure X => μ.val B) := by
  let m : MeasurableSpace (CountingMeasure X) :=
    MeasurableSpace.generateFrom (generatingSets X)
  apply Measurable.of_le_map
  intro D _
  exact mapSetsAreMeasurable D B hB

/-- 𝓝(X) ≤ σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem restrictedSigmaAlgebraIsIngeneratedSigmaAlgebra
    (X : Type*) [MeasurableSpace X] :
    (inferInstance : MeasurableSpace (CountingMeasure X)) ≤
    MeasurableSpace.generateFrom (generatingSets X) := by
  apply measurable_iff_comap_le.mp
  refine Measure.measurable_measure.mpr ?_
  intro B hB
  exact evaluationMapIsGeneratedMeasurable B hB







/-- 𝓝(X) =  σ ({μ ∈ N(X) : μ(B) = k}: B ∈ χ, k ∈ ℕ }) -/
theorem sigmaAlgebraIsGenerated
    (X : Type*) [MeasurableSpace X] :
    (inferInstance : MeasurableSpace (CountingMeasure X)) =
      MeasurableSpace.generateFrom (generatingSets X) := by
  apply le_antisymm
  · exact restrictedSigmaAlgebraIsIngeneratedSigmaAlgebra X
  · exact generatedSigmaAlgebraInRestrictedSigmaAlgebra X


end PenroseAndLast
