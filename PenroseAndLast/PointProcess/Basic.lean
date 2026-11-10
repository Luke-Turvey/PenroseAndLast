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


/-- A finite counting measure is a measure taking natural number values
on every measurable set. -/
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
sum of finite counting measures. -/
def IsCountingMeasure
  {X : Type*} [MeasurableSpace X]
  (μ : Measure X) : Prop :=
  ∃ (α : ℕ → Measure X) , (∀ i : ℕ, IsFiniteCountingMeasure (α i))
  ∧ μ = Measure.sum α

@[expose]
def CountingMeasure
    (X : Type*) [MeasurableSpace X] :=
  { μ : Measure X // IsCountingMeasure μ}

/-- Every finite counting measure is a counting measure -/
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


end PenroseAndLast
