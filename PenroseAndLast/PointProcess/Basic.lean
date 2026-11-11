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

This file introduces point processes as random counting measures,
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






end PenroseAndLast
