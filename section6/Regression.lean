import CircularLawSection6

open Filter Topology Set Polynomial Real
open CircularLawSection6 CircularLawSections56.Section6

-- The zero polynomial and zero constant term do not break radial monotonicity.
example : MonotoneOn (polynomialCircleMean 0) (Ioi 0) :=
  polynomialCircleMean_monotoneOn 0

example : MonotoneOn (polynomialCircleMean X) (Ioi 0) :=
  polynomialCircleMean_monotoneOn X

-- A root on the unit circle is allowed; the logarithmic singularity is integrable.
example : polynomialCircleMean (X - C (1 : ℂ)) 1 = 0 := by
  simp [polynomialCircleMean]

-- Empty matrices use the explicitly totalized normalized average.
example (A B : Matrix (Fin 0) (Fin 0) ℂ) :
    Real.log ‖A.det‖ / (0 : ℝ) ≤
      circleAverage (fun w => Real.log ‖(w • B + A).det‖) 0 1 / (0 : ℝ) := by
  simp

-- Constant polynomials retain their actual constant term in Jensen's inequality.
example (a : ℂ) (ha : a ≠ 0) :
    Real.log ‖a‖ ≤ polynomialCircleMean (C a) 1 := by
  simpa using log_norm_eval_zero_le_polynomialCircleMean (C a) (by simpa using ha)

-- The spectral origin and the joining radius of the circular potential are allowed.
example {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 1)) :
    Tendsto (fun R => varianceScaledRadialPotential (v R) 0) atTop
      (𝓝 (circularRadialPotential 0)) :=
  varianceScaledRadialPotential_tendsto_one hv 0

example : ContinuousAt circularRadialPotential 1 :=
  continuous_circularRadialPotential.continuousAt
