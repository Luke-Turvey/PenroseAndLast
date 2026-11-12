/-
Copyright (c) 2026 Luke Turvey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Turvey
-/
module

public import Mathlib
public import PenroseAndLast.CountingMeasure.Defs
public import PenroseAndLast.CountingMeasure.Measurability

/-!
# Point Processes

This file introduces point processes as measurable maps from
a "probability" space to the space of counting measures,
following Chapter 2 Lectures on the Poisson Process (2017)
by Gunter Last and Matthew Penrose,
-/

public section

namespace PenroseAndLast

open MeasureTheory

open scoped ENNReal

def IsPointProcess
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (η : Ω → CountingMeasure X) : Prop :=
    Measurable η

@[expose]
def PointProcess
    (X Ω : Type*)
    [MeasurableSpace X] [MeasurableSpace Ω] :=
  {η : (Ω → CountingMeasure X) // IsPointProcess η}

/-- ∀ B ∈ χ, η (ω) (B) is a measurable function from Ω → [0,∞] -/
theorem PointProcess.measurable_eval
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (η : Ω → CountingMeasure X)
    (hη : IsPointProcess η) :
    ∀ B : Set X, MeasurableSet B →
      Measurable (fun ω : Ω => (η ω).val B) := by
  intro B hB
  have heval : Measurable (fun μ : CountingMeasure X => μ.val B) := by
    exact CountingMeasure.measurable_eval B hB
  apply heval.comp hη

/-- ∀ B ∈ χ, {η (ω) (B) = k} is measurable in (Ω,F) -/
theorem PointProcess.measurableSet_eval
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (η : Ω → CountingMeasure X)
    (hη : IsPointProcess η) :
    ∀ k : ENNReal, ∀ B : Set X, MeasurableSet B →
      MeasurableSet ({ ω : Ω | (η ω).val B = (k : ENNReal)} : Set Ω) := by
  intro k B hB
  apply measurableSet_setOfPred.mpr
  refine Measurable.eq_const ?_ k
  exact PointProcess.measurable_eval η hη B hB

/-- Take a  map Y : Ω → X) and let δ_Y(ω) be the dirac measure at Y(ω).
Note measurability of Y is not assumed in the definition -/
noncomputable def PointProcess.onePoint
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (Y : Ω → X) :
    Ω → CountingMeasure X :=
  fun ω => CountingMeasure.dirac (Y ω)

/-- The one point function with the additional measurability assumption
on Y is a point process. -/
theorem IsPointProcess.onePoint_process
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (Y : Ω → X)
    (hY : Measurable Y) :
    IsPointProcess (fun ω => CountingMeasure.dirac (Y ω)) := by
  exact Measurable.fun_comp CountingMeasure.dirac_measurable hY

/-- Define the onePoint process as a subtype of PointProcess -/
noncomputable def PointProcess.onePoint_process
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (Y : Ω → X)
    (hY : Measurable Y) :
    PointProcess X Ω :=
  ⟨PointProcess.onePoint Y, IsPointProcess.onePoint_process Y hY⟩

/-- Sum of two point processes is a point process -/
theorem IsPointProcess.sum
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (η ξ : Ω → CountingMeasure X)
    (hη : IsPointProcess η)
    (hξ : IsPointProcess ξ) :
    IsPointProcess (η + ξ : Ω → CountingMeasure X) := by
  exact Measurable.add hη hξ

theorem IsPointProcess.zero
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] :
    IsPointProcess (0 : Ω → CountingMeasure X) := by
  exact measurable_zero

/-- Sum of n point processes is a point process -/
theorem IsPointProcess.n_sum
    {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (f : ℕ → (Ω → CountingMeasure X))
    (hf : ∀ i : ℕ, IsPointProcess (f i))
    (n : ℕ) :
    IsPointProcess (∑ i ∈ Finset.range n, f i) := by
  change Measurable (∑ i ∈ Finset.range n, f i)
  rw [Finset.sum_fn]
  apply Finset.measurable_sum
  intro i hi
  exact hf i




end PenroseAndLast
