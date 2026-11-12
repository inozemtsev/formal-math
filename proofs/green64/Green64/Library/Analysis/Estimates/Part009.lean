module

public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.SourcePeeledFullSumReindex
public import Mathlib
public import Green64.Library.Correlation.Part002
public import Green64.Library.Weights.Part011
public import Green64.Library.Weights.Part039
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part041
public import Green64.Library.Weights.Part020
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part040
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Correlation.Part003
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part023

@[expose] public section

/-!
# Analysis / Estimates / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## code.SourceArcCharacters -/

section

set_option maxHeartbeats 8000000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- The gcd quotient modulus is positive, including rprime=0. -/
theorem source_reduced_modulus_pos (rprime r : ℕ) (hr : 0 < r) :
    0 < r / Nat.gcd rprime r := by
  have hgd : Nat.gcd rprime r ∣ r := Nat.gcd_dvd_right rprime r
  have hgp : 0 < Nat.gcd rprime r := Nat.gcd_pos_of_pos_right rprime hr
  exact Nat.div_pos (Nat.le_of_dvd hr hgd) hgp

/-- Exact additive rational character phase on a ZMod-unit residue. -/
noncomputable def sourceUnitPhase (q : ℕ) [NeZero q]
    (h : ℕ) (u : (ZMod q)ˣ) : ℂ :=
  Complex.exp (((2 * Real.pi * (h:ℝ) *
    (((u : ZMod q).val : ℝ) / (q:ℝ)) : ℝ) : ℂ) * Complex.I)

theorem sourceUnitPhase_norm_one (q : ℕ) [NeZero q]
    (h : ℕ) (u : (ZMod q)ˣ) :
    ‖sourceUnitPhase q h u‖ = 1 := by
  unfold sourceUnitPhase
  rw [Complex.norm_exp]
  simp

/-- Literal finite Fourier expansion of the source rational phase, for
    every modulus including q=1 and every Dirichlet character. -/
theorem source_unit_phase_character_expansion
    (q h v : ℕ) [NeZero q] (hv : Nat.Coprime v q) :
    ∃ u : (ZMod q)ˣ, (u : ZMod q) = (v : ZMod q) ∧
      (sourceUnitPhase q h u =
        ∑ χ : DirichletCharacter ℂ q,
          ((q.totient : ℂ)⁻¹ *
             ∑ w : (ZMod q)ˣ, sourceUnitPhase q h w *
               star (χ (w : ZMod q))) *
                 χ (u : ZMod q)) ∧
      (∀ χ : DirichletCharacter ℂ q,
        ‖(q.totient : ℂ)⁻¹ *
          ∑ w : (ZMod q)ˣ, sourceUnitPhase q h w *
            star (χ (w : ZMod q))‖ ≤ 1) := by
  classical
  have hunit : IsUnit (v : ZMod q) :=
    (ZMod.isUnit_iff_coprime v q).mpr hv
  let u : (ZMod q)ˣ := hunit.unit
  have hu : (u : ZMod q) = (v : ZMod q) := hunit.unit_spec
  have hnorm : ∀ w : (ZMod q)ˣ,
      ‖sourceUnitPhase q h w‖ ≤ 1 := by
    intro w
    rw [sourceUnitPhase_norm_one]
  obtain ⟨hexp, hcoef⟩ :=
    Green64CorrelationFinite.characterExpansion q (sourceUnitPhase q h) hnorm
  exact ⟨u, hu, hexp u, hcoef⟩
end Green64Analytic.CorrelationD

end

/-! ## code.SourcePhaseReduction -/

section

set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationD

/-- The unreduced rational-center exponential in the actual integer argument. -/
noncomputable def sourceRationalPhase (q h v : ℕ) : ℂ :=
  Complex.exp (((h:ℂ)*(v:ℂ))/(q:ℂ) *
    (2 * (Real.pi:ℂ) * Complex.I))

theorem sourceRationalPhase_mod (q h v : ℕ) (hq : 0 < q) :
    sourceRationalPhase q h v = sourceRationalPhase q h (v % q) := by
  have hqc : (q:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hnat : v % q + q * (v / q) = v := Nat.mod_add_div v q
  have hcast : (v:ℂ) = ((v%q:ℕ):ℂ) + (q:ℂ) * (((v/q:ℕ):ℂ)) := by
    have hh := congrArg (fun n : ℕ => (n : ℂ)) hnat.symm
    simpa only [Nat.cast_add, Nat.cast_mul] using hh
  unfold sourceRationalPhase
  calc
    Complex.exp (((h:ℂ)*(v:ℂ))/(q:ℂ) * (2*(Real.pi:ℂ)*Complex.I))
      = Complex.exp (
          (((h:ℂ)*(((v%q:ℕ):ℂ)))/(q:ℂ) * (2*(Real.pi:ℂ)*Complex.I)) +
          ((h*(v/q):ℕ):ℂ) * (2*(Real.pi:ℂ)*Complex.I)) := by
            congr 1
            rw [hcast]
            field_simp
            rw [Nat.cast_mul]
            ring
    _ = _ := by
      rw [Complex.exp_add]
      simp only [Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem sourceUnitPhase_eq_rational_phase
    (q h : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    sourceUnitPhase q h u =
      sourceRationalPhase q h ((u:ZMod q).val) := by
  unfold sourceUnitPhase sourceRationalPhase
  congr 1
  push_cast
  ring

/-- The original integer phase equals the character-unit residue phase. -/
theorem sourceRationalPhase_of_unit
    (q h v : ℕ) [NeZero q] (hq : 0 < q)
    (u : (ZMod q)ˣ) (hu : (u:ZMod q) = (v:ZMod q)) :
    sourceRationalPhase q h v = sourceUnitPhase q h u := by
  rw [sourceRationalPhase_mod q h v hq]
  rw [← ZMod.val_natCast q v, ← hu]
  exact (sourceUnitPhase_eq_rational_phase q h u).symm
end Green64Analytic.CorrelationD

end

/-! ## code.SourceCharacterProduct -/

section

set_option maxHeartbeats 8000000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

noncomputable def sourceCharacterCoefficient (q : ℕ) [NeZero q]
    (h : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient : ℂ)⁻¹ *
    ∑ u : (ZMod q)ˣ, sourceUnitPhase q h u *
      star (χ (u : ZMod q))

theorem source_character_fourfactor_mul
    (q m ps p residual : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    χ ((m * ps * p * residual : ℕ) : ZMod q) =
      χ (m : ZMod q) * χ (ps : ZMod q) *
        χ (p : ZMod q) * χ (residual : ZMod q) := by
  push_cast
  simp only [map_mul]

/-- Exact rational phase on the original natural integer, not merely
    on a representative unit. Coefficient bound includes q=1. -/
theorem source_rational_phase_fourier
    (q h v : ℕ) [NeZero q] (hq : 0 < q)
    (hv : Nat.Coprime v q) :
    sourceRationalPhase q h v =
        ∑ χ : DirichletCharacter ℂ q,
          sourceCharacterCoefficient q h χ * χ (v : ZMod q) ∧
    (∀ χ : DirichletCharacter ℂ q,
       ‖sourceCharacterCoefficient q h χ‖ ≤ 1) := by
  obtain ⟨u, hu, hexp, hcoeff⟩ :=
    source_unit_phase_character_expansion q h v hv
  constructor
  · calc
      _ = sourceUnitPhase q h u := sourceRationalPhase_of_unit q h v hq u hu
      _ = ∑ χ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h χ * χ (u : ZMod q) := by
          simpa only [sourceCharacterCoefficient] using hexp
      _ = _ := by simp only [hu]
  · exact hcoeff
end Green64Analytic.CorrelationD

end

/-! ## code.SourceGcdPhase -/

section

set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationD

/-- Exact reduction of the *original rational-center exponential*
    from denominator r to q=r/gcd(rprime,r). No phase term is lost. -/
theorem source_phase_gcd_reduction
    (h v rprime r : ℕ) (hr : 0 < r) :
    sourceRationalPhase r h (v*rprime) =
      sourceRationalPhase (r/Nat.gcd rprime r) h
        (v*(rprime/Nat.gcd rprime r)) := by
  let d := Nat.gcd rprime r
  change sourceRationalPhase r h (v*rprime) =
    sourceRationalPhase (r/d) h (v*(rprime/d))
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_right rprime hr
  have hqPos : 0 < r/d := source_reduced_modulus_pos rprime r hr
  have hdNe : (d:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdPos)
  have hqNe : ((r/d:ℕ):ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqPos)
  have hrDiv : (r/d)*d = r := Nat.div_mul_cancel (Nat.gcd_dvd_right rprime r)
  have hpDiv : (rprime/d)*d = rprime :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left rprime r)
  have hNr : (r:ℂ) = (((r/d:ℕ):ℂ))*(d:ℂ) := by
    have hh := congrArg (fun n : ℕ => (n:ℂ)) hrDiv.symm
    simpa only [Nat.cast_mul] using hh
  have hNv : ((v*rprime:ℕ):ℂ) =
      ((v*(rprime/d):ℕ):ℂ) * (d:ℂ) := by
    have hh : v*rprime = (v*(rprime/d))*d := by
      calc
        v*rprime = v*((rprime/d)*d) := congrArg (fun t : ℕ => v*t) hpDiv.symm
        _ = (v*(rprime/d))*d := by ring
    exact_mod_cast hh
  unfold sourceRationalPhase
  congr 1
  rw [hNv, hNr]
  push_cast
  field_simp
end Green64Analytic.CorrelationD

end

/-! ## code.SourceRationalCharacterAssembly -/

section

set_option maxHeartbeats 8000000
open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Exact original rational-center exponential as a character sum of
    the four literal source factors. No analytic minor-arc input is used. -/
theorem source_rational_center_character
    (m ps p rprime r h q : ℕ) (L a τ C : ℝ)
    [NeZero q]
    (hr : 0 < r) (hq : q = r/Nat.gcd rprime r)
    (hrcap : (r:ℝ) ≤ L^C)
    (hrough : SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hpsPrime : ps.Prime)
    (hps : Real.exp (L^a) ≤ (ps:ℝ))
    (hsmall : L^C < Real.exp (L^a))
    (hpPrime : p.Prime)
    (hp : Real.exp (τ*L) ≤ (p:ℝ))
    (hlong : L^C < Real.exp (τ*L)) :
    (sourceRationalPhase r h (m*ps*p*rprime) =
      ∑ χ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h χ *
          χ (m:ZMod q) * χ (ps:ZMod q) *
          χ (p:ZMod q) *
          χ ((rprime/Nat.gcd rprime r:ℕ):ZMod q)) ∧
    (∀ χ : DirichletCharacter ℂ q,
       ‖sourceCharacterCoefficient q h χ‖ ≤ 1) := by
  have hqPos : 0 < q := by
    rw [hq]
    exact source_reduced_modulus_pos rprime r hr
  have hv : Nat.Coprime
      (m*ps*p*(rprime/Nat.gcd rprime r)) q := by
    rw [hq]
    exact source_four_factor_unit m ps p rprime r L a τ C
      hr hrcap hrough hW hpsPrime hps hsmall hpPrime hp hlong
  obtain ⟨hfourier, hcoeff⟩ :=
    source_rational_phase_fourier q h
      (m*ps*p*(rprime/Nat.gcd rprime r)) hqPos hv
  constructor
  · calc
      sourceRationalPhase r h (m*ps*p*rprime)
        = sourceRationalPhase (r/Nat.gcd rprime r) h
          ((m*ps*p)*(rprime/Nat.gcd rprime r)) := by
            convert source_phase_gcd_reduction h (m*ps*p) rprime r hr using 1 <;>
              ring
      _ = sourceRationalPhase q h
        (m*ps*p*(rprime/Nat.gcd rprime r)) := by rw [hq]
      _ = ∑ χ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h χ *
          χ ((m*ps*p*(rprime/Nat.gcd rprime r):ℕ):ZMod q) :=
            hfourier
      _ = _ := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [source_character_fourfactor_mul]
        ring
  · exact hcoeff
end Green64Analytic.CorrelationD

end

/-! ## SourcePeeledRationalGcdBridge -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin

/-- The gcd-conditioned character residual agrees EXACTLY with the
original raw source residual times the post-expansion character. -/
theorem source_raw_to_physical_gcd
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den r : ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k G Parity c den (Nat.gcd r den) q χ 0 r =
      sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k G Parity c r * χ (r / Nat.gcd r den) := by
  simp only [sourcePhysicalMarkedResidual, ite_true,
    sourceRawMarkedResidual, sourceUnitTwist]
  simp
  ring

/-- Exact four-character expansion at the true r'-dependent gcd
class; no scale assumptions are used beyond genuine coprimality. -/
theorem source_peeled_rational_fourfactor_gcd
    (m ps p r den h : ℕ) (hden : 0 < den)
    (hunit : Nat.Coprime
      (m*ps*p*(r/Nat.gcd r den)) (den/Nat.gcd r den)) :
    let d := Nat.gcd r den
    let q := den/d
    letI : NeZero q := ⟨Nat.ne_of_gt
      (source_reduced_modulus_pos r den hden)⟩
    sourceRationalPhase den h (m*ps*p*r) =
      ∑ χ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h χ *
          χ (m:ZMod q) * χ (ps:ZMod q) *
          χ (p:ZMod q) * χ ((r/d:ℕ):ZMod q) := by
  dsimp only
  let q := den/Nat.gcd r den
  have hq : 0 < q := source_reduced_modulus_pos r den hden
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hFourier := (source_rational_phase_fourier q h
    (m*ps*p*(r/Nat.gcd r den)) hq hunit).1
  calc
    sourceRationalPhase den h (m*ps*p*r) =
      sourceRationalPhase q h
        (m*ps*p*(r/Nat.gcd r den)) := by
      simpa only [q] using
        (source_phase_gcd_reduction h (m*ps*p) r den hden)
    _ = ∑ χ : DirichletCharacter ℂ q,
       sourceCharacterCoefficient q h χ *
         χ ((m*ps*p*(r/Nat.gcd r den):ℕ):ZMod q) :=
         hFourier
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [source_character_fourfactor_mul]
      ring

/-- The rationally twisted individual source term is a genuinely
character-expanded physical d_{r'} at the actual gcd class. -/
theorem source_peeled_rational_physical_term
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (G Parity : Finset ℕ) (α c : ℕ → ℂ)
    (χ0 : DirichletCharacter ℂ qBase) (σ₀ σ₁ : ℝ)
    (m ps p r den h : ℕ) (hden : 0 < den)
    (hunit : Nat.Coprime
      (m*ps*p*(r/Nat.gcd r den)) (den/Nat.gcd r den)) :
    let d := Nat.gcd r den
    let q := den/d
    letI : NeZero q := ⟨Nat.ne_of_gt
      (source_reduced_modulus_pos r den hden)⟩
    sourceRationalPhase den h (m*ps*p*r) *
      ((α m * χ0 m * sourceUnitTwist m σ₀ *
          sourceUnitTwist p σ₁) *
       (((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps) *
       sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb b k G Parity c r) =
      ∑ χ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h χ *
          ((α m * χ0 m * sourceUnitTwist m σ₀ * χ (m:ZMod q)) *
           (((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps *
              χ (ps:ZMod q)) *
           (sourceUnitTwist p σ₁ * χ (p:ZMod q)) *
           sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k G Parity c den d q χ 0 r) := by
  dsimp only
  let d := Nat.gcd r den
  let q := den/d
  have hq : 0 < q := source_reduced_modulus_pos r den hden
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hphase := source_peeled_rational_fourfactor_gcd
    m ps p r den h hden hunit
  dsimp only at hphase
  rw [hphase, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [source_raw_to_physical_gcd]
  ring

/-- Complete rational-center sum with the actual gcd- and
character-filtered d_{r'}. Character modulus varies with r'.
No representations are identified, discarded, or counted twice. -/
theorem source_peeled_rational_full_physical_reindex
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ)
    (hn : 0 < n) (hden : 0 < den)
    (hSG : S ⊆ G) (hParityG : Parity ⊆ G)
    (hTsG : ∀ g, Ts g ⊆ G)
    (hTbG : ∀ g, Tb g ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (hunit : ∀ z ∈ sourcePeeledQuadIndices G S primeSlot n,
       α z.1.1 ≠ 0 →
       Nat.Coprime
         (z.1.1*z.1.2*z.2.1*
           (z.2.2/Nat.gcd z.2.2 den))
         (den/Nat.gcd z.2.2 den)) :

    sourceRationalPhase den h n *
      (literalSourceParity Parity n *
        ((∑ m ∈ (sourceOutsidePart G n).divisors,
          ∑ p ∈ (sourceOutsidePart G n).divisors,
            if p ∈ primeSlot ∧ p.Prime ∧
              m*p ∣ sourceOutsidePart G n then
              α m * χ0 m * sourceUnitTwist m σ₀ *
                sourceUnitTwist p σ₁ *
                c (sourceOutsidePart G n/(m*p))
            else 0) *
        (((1/Vs:ℝ):ℂ) *
          ∑ ps ∈ smallPrimeSupport S n,
            literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k (n/ps)))) =
    ∑ z ∈ sourcePeeledQuadIndices G S primeSlot n,
      let d := Nat.gcd z.2.2 den
      let q := den/d
      letI : NeZero q := ⟨Nat.ne_of_gt
        (source_reduced_modulus_pos z.2.2 den hden)⟩
      ∑ ξ : DirichletCharacter ℂ q,
        sourceCharacterCoefficient q h ξ *
          ((α z.1.1 * χ0 z.1.1 * sourceUnitTwist z.1.1 σ₀ *
               ξ (z.1.1:ZMod q)) *
           (((1/Vs:ℝ):ℂ) * literalSourceParity Parity z.1.2 *
               ξ (z.1.2:ZMod q)) *
           (sourceUnitTwist z.2.1 σ₁ * ξ (z.2.1:ZMod q)) *
           sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
             ts tb b k G Parity c den d q ξ 0 z.2.2) := by

  classical
  have hRaw := source_peeled_full_sum_to_raw_residual
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
    ts tb b k qBase α c χ0 σ₀ σ₁ n hn
    hSG hParityG hTsG hTbG hSPrime hTsPrime hTbPrime
  rw [hRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hprod :=
    source_peeled_quad_product_exact G S primeSlot n hn hSG hSPrime z hz
  rw [← hprod]
  by_cases hα0 : α z.1.1 = 0
  · simp [hα0]
  · exact source_peeled_rational_physical_term
      S Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase
      G Parity α c χ0 σ₀ σ₁
      z.1.1 z.1.2 z.2.1 z.2.2 den h hden
      (hunit z hz hα0)

/-- Unit hypotheses on the ACTUAL source four-factor indices follow
from the original rough-alpha support and the two prime scales. -/
theorem source_peeled_rational_source_units
    (G S primeSlot : Finset ℕ) (n den : ℕ)
    (α : ℕ → ℂ) (L a τ C : ℝ)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (τ*L))
    (hαSupport : ∀ m, α m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSPrime : ∀ ps ∈ S, ps.Prime)
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (τ*L) ≤ (p:ℝ)) :
    ∀ z ∈ sourcePeeledQuadIndices G S primeSlot n,
      α z.1.1 ≠ 0 →
      Nat.Coprime (z.1.1*z.1.2*z.2.1*
        (z.2.2/Nat.gcd z.2.2 den))
        (den/Nat.gcd z.2.2 den) := by
  classical
  intro z hz hα
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
  have htPair := (Finset.mem_filter.mp ht).1
  have hps := (Finset.mem_product.mp htPair).2
  have hpsS : t.2 ∈ S := (Finset.mem_filter.mp hps).1
  have hprimeSlot := (Finset.mem_filter.mp ht).2.1
  have hpPrime := (Finset.mem_filter.mp ht).2.2.1
  have hunit := source_four_factor_unit
    t.1.1 t.2 t.1.2 (n/(t.1.1*t.2*t.1.2))
    den L a τ C hden hdenCap
    (hαSupport t.1.1 hα) hW
    (hSPrime t.2 hpsS) (hSRange t.2 hpsS) hsmall
    hpPrime (hSlotRange t.1.2 hprimeSlot) hlong
  simpa only [sourcePeeledQuadEncode] using hunit

/-- Canonical full rational-character coefficient from the source,
with the true gcd class of each r' and no omitted character. -/
noncomputable def sourcePeeledPhysicalCharacterSum
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ) (hden : 0 < den) : ℂ :=
  ∑ z ∈ sourcePeeledQuadIndices G S primeSlot n,
    let d := Nat.gcd z.2.2 den
    let q := den/d
    letI : NeZero q := ⟨Nat.ne_of_gt
      (source_reduced_modulus_pos z.2.2 den hden)⟩
    ∑ ξ : DirichletCharacter ℂ q,
      sourceCharacterCoefficient q h ξ *
        ((α z.1.1 * χ0 z.1.1 * sourceUnitTwist z.1.1 σ₀ *
             ξ (z.1.1:ZMod q)) *
         (((1/Vs:ℝ):ℂ) * literalSourceParity Parity z.1.2 *
             ξ (z.1.2:ZMod q)) *
         (sourceUnitTwist z.2.1 σ₁ * ξ (z.2.1:ZMod q)) *
         sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
           ts tb b k G Parity c den d q ξ 0 z.2.2)

/-- Full extracted ORIGINAL Fourier coefficient at a rational center:
it equals the actual gcd/character-expanded source physical residual
sum, including all representations and every induced character.

The coprimality preconditions are proved here from the literal
source roughness and prime-range restrictions, not postulated. -/
theorem source_original_fourier_rational_physical_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ0 : DirichletCharacter ℂ qBase) (σ₀ σ₁ : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
       ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L a τ C : ℝ) (n den h : ℕ)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (τ*L))

    (hαSupport : ∀ m, α m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (τ*L) ≤ (p:ℝ)) :
    sourceRationalPhase den h n *
      fourierCoeff (T:=1)
        (sourcePeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
           ts tb b k primeSlot Ptwist α c χ0 σ₀ σ₁) (n:ℤ) =
      if n ∈ Finset.Icc 1 N then
        sourcePeeledPhysicalCharacterSum G Ptwist S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
          n den h hden
      else 0 := by
  classical
  rw [source_peeled_fourier_triple_coefficient_exact]
  by_cases hI : n ∈ Finset.Icc 1 N
  · simp only [hI, ite_true]
    have hn : 0 < n := (Finset.mem_Icc.mp hI).1
    have hSG : S ⊆ G := by
      intro v hv
      rw [hG]
      simp [hv]
    have hTsG : ∀ g, Ts g ⊆ G := by
      intro g v hv
      rw [hG]
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨g, Finset.mem_univ _, hv⟩)

    have hTbG : ∀ g, Tb g ⊆ G := by
      intro g v hv
      rw [hG]
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨g, Finset.mem_univ _, hv⟩
    have hUnits := source_peeled_rational_source_units
      G S primeSlot n den α L a τ C hden hdenCap
      hW hsmall hlong hαSupport hSPrime hSRange hSlotRange
    have hExact := source_peeled_rational_full_physical_reindex
      G Ptwist S primeSlot Ts Tb q0 Vs Vsmall Vbig
      ts tb b k qBase α c χ0 σ₀ σ₁ n den h hn hden
      hSG hParityG hTsG hTbG hSPrime hTsPrime hTbPrime hUnits
    simpa only [← hG, sourcePeeledPhysicalCharacterSum] using hExact
  · simp only [hI, ite_false, mul_zero]
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeeledGroupedGcdCharacters -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin

theorem source_divisor_quotient_pos
    (den d : ℕ) (hden : 0 < den)
    (hd : d ∈ den.divisors) : 0 < den/d := by
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_dvd_of_pos hdiv hden
  exact Nat.div_pos (Nat.le_of_dvd hden hdiv) hdpos

def sourceActualGcdClass (den : ℕ) (hden : 0 < den)
    (r : ℕ) : {d : ℕ // d ∈ den.divisors} :=
  ⟨Nat.gcd r den,
    Nat.mem_divisors.mpr
      ⟨Nat.gcd_dvd_right r den, Nat.ne_of_gt hden⟩⟩

/-- Finite gcd fiber grouping; no injectivity is needed and every
source representation remains present with its original multiplicity. -/
theorem source_subtype_gcd_group
    {Z D : Type} [DecidableEq Z] [Fintype D] [DecidableEq D]
    (Q : Finset Z) (g : Z → D) (F : D → Z → ℂ) :
    (∑ z ∈ Q, F (g z) z) =
      ∑ d : D, ∑ z ∈ Q.filter (fun z => g z = d), F d z := by
  classical
  calc
    _ = ∑ z ∈ Q, ∑ d : D, if g z = d then F d z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp
    _ = ∑ d : D, ∑ z ∈ Q, if g z = d then F d z else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.sum_filter]

/-- A fixed gcd-class and fixed rational character coefficient. This
is the component used as one four-factor Mellin polynomial. -/
noncomputable def sourcePeeledFixedGcdCharacterTerm
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (den h : ℕ) (hden : 0 < den)
    (d : {d : ℕ // d ∈ den.divisors})
    (ξ : DirichletCharacter ℂ (den/(d:ℕ)))
    (z : ((ℕ × ℕ) × (ℕ × ℕ))) : ℂ :=
  let q := den/(d:ℕ)
  letI : NeZero q := ⟨Nat.ne_of_gt
    (source_divisor_quotient_pos den d.1 hden d.2)⟩
  sourceCharacterCoefficient q h ξ *
    ((α z.1.1 * χ0 z.1.1 * sourceUnitTwist z.1.1 σ₀ *
         ξ (z.1.1:ZMod q)) *
     (((1/Vs:ℝ):ℂ) * literalSourceParity Parity z.1.2 *
         ξ (z.1.2:ZMod q)) *
     (sourceUnitTwist z.2.1 σ₁ * ξ (z.2.1:ZMod q)) *
     sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
       ts tb b k G Parity c den d.1 q ξ 0 z.2.2)

/-- The FULL expression with true fixed (gcd d, character ξ) outside
the inner source factorization sum; exactly the TeX quantifier order. -/
noncomputable def sourcePeeledGroupedPhysicalSum
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ) (hden : 0 < den) : ℂ :=
  ∑ d : {d : ℕ // d ∈ den.divisors},
    ∑ ξ : DirichletCharacter ℂ (den/(d:ℕ)),
      ∑ z ∈ (sourcePeeledQuadIndices G S primeSlot n).filter
          (fun z => Nat.gcd z.2.2 den = (d:ℕ)),
        sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
          den h hden d ξ z

/-- The per-residual character sums are EXACTLY the fully grouped
(gcd class, character, source representation) sums, with no losses. -/
theorem source_peeled_physical_gcd_grouped
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ) (hden : 0 < den) :
    sourcePeeledPhysicalCharacterSum G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁ n den h hden =
    sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁ n den h hden := by
  classical
  let Q : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
    sourcePeeledQuadIndices G S primeSlot n
  let D := {d : ℕ // d ∈ den.divisors}
  let g : ((ℕ×ℕ)×(ℕ×ℕ)) → D :=
    fun z => sourceActualGcdClass den hden z.2.2

  let F : D → ((ℕ×ℕ)×(ℕ×ℕ)) → ℂ := fun d z =>
    ∑ ξ : DirichletCharacter ℂ (den/(d:ℕ)),
      sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
        q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
        den h hden d ξ z
  have hL :
      sourcePeeledPhysicalCharacterSum G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁ n den h hden =
        ∑ z ∈ Q, F (g z) z := by
      rfl
  calc
    _ = ∑ z ∈ Q, F (g z) z := hL
    _ = ∑ d : D, ∑ z ∈ Q.filter (fun z => g z = d), F d z :=
      source_subtype_gcd_group Q g F
    _ = _ := by
      unfold sourcePeeledGroupedPhysicalSum
      apply Finset.sum_congr rfl
      intro d hd
      have hFilter : Q.filter (fun z => g z = d) =
          Q.filter (fun z => Nat.gcd z.2.2 den = (d:ℕ)) := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · intro hz
          exact ⟨hz.1, congrArg Subtype.val hz.2⟩
        · intro hz
          exact ⟨hz.1, Subtype.ext hz.2⟩
      rw [hFilter]
      simp only [F]
      rw [Finset.sum_comm]

end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeeledGroupedOriginalFourier -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Strongest exact source bridge: the ORIGINAL Fourier coefficient
at a rational center equals a finite sum indexed, in this order, by
the true gcd divisor d', a character modulo den/d', and every
ordered source factorization m,p_s,p,r'. No new bijection assumption. -/
theorem source_original_fourier_grouped_physical_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ0 : DirichletCharacter ℂ qBase) (σ₀ σ₁ : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
       ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)

    (L a τ C : ℝ) (n den h : ℕ)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (τ*L))
    (hαSupport : ∀ m, α m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (τ*L) ≤ (p:ℝ)) :
    sourceRationalPhase den h n *
      fourierCoeff (T:=1)
        (sourcePeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
           ts tb b k primeSlot Ptwist α c χ0 σ₀ σ₁) (n:ℤ) =
      if n ∈ Finset.Icc 1 N then
        sourcePeeledGroupedPhysicalSum G Ptwist S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
          n den h hden
      else 0 := by
  have hSource := source_original_fourier_rational_physical_exact
      N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ0 σ₀ σ₁ G
      hG hParityG hSPrime hTsPrime hTbPrime L a τ C
      n den h hden hdenCap hW hsmall hlong
      hαSupport hSRange hSlotRange
  rw [source_peeled_physical_gcd_grouped] at hSource
  exact hSource
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDisjointGroupedDyads -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

noncomputable def sourcePeeledDisjointDyadicPhysicalSum434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ) (hden : 0 < den) : ℂ :=
  ∑ d : {d : ℕ // d ∈ den.divisors},
    ∑ ξ : DirichletCharacter ℂ (den/(d:ℕ)),
      ∑ j ∈ ((sourcePeeledQuadIndices G S primeSlot n).filter
          (fun z => Nat.gcd z.2.2 den = (d:ℕ))).image sourceQuadDyadIndex434,
        ∑ z ∈ ((sourcePeeledQuadIndices G S primeSlot n).filter
          (fun z => Nat.gcd z.2.2 den = (d:ℕ))).filter
          (fun z => sourceQuadDyadIndex434 z = j),
        sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
          den h hden d ξ z

theorem source_grouped_physical_disjoint_dyads434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (α c : ℕ → ℂ) (χ0 : DirichletCharacter ℂ qBase)
    (σ₀ σ₁ : ℝ) (n den h : ℕ) (hden : 0 < den) :
    sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁ n den h hden =
    sourcePeeledDisjointDyadicPhysicalSum434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁ n den h hden := by
  classical
  unfold sourcePeeledGroupedPhysicalSum sourcePeeledDisjointDyadicPhysicalSum434
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro ξ hξ
  exact source_canonical_dyad_sum434 _ _
theorem source_original_fourier_disjoint_dyadic_physical_exact434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ0 : DirichletCharacter ℂ qBase) (σ₀ σ₁ : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
       ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)

    (L a τ C : ℝ) (n den h : ℕ)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (τ*L))
    (hαSupport : ∀ m, α m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (τ*L) ≤ (p:ℝ)) :
    sourceRationalPhase den h n *
      fourierCoeff (T:=1)
        (sourcePeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
           ts tb b k primeSlot Ptwist α c χ0 σ₀ σ₁) (n:ℤ) =
      if n ∈ Finset.Icc 1 N then
        sourcePeeledDisjointDyadicPhysicalSum434 G Ptwist S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase α c χ0 σ₀ σ₁
          n den h hden
      else 0 := by
  rw [← source_grouped_physical_disjoint_dyads434]
  exact source_original_fourier_grouped_physical_exact
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Ptwist α c χ0 σ₀ σ₁ G
    hG hParityG hSPrime hTsPrime hTbPrime L a τ C n den h hden
    hdenCap hW hsmall hlong hαSupport hSRange hSlotRange
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCartesianInverse -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/-- Original rough support removes all marked group primes; no new
support hypothesis replaces the source roughness condition. -/
theorem source_rough_alpha_no_group434
    (G : Finset ℕ) (m : ℕ) (W : ℝ)
    (hG : ∀ v ∈ G, (v:ℝ) ≤ W) (hm : SourceRoughAbove m W) :
    ∀ v ∈ m.primeFactors, v ∉ G := by
  intro v hv hvG
  obtain ⟨hvPrime,hvDiv,_⟩ := Nat.mem_primeFactors.mp hv
  exact (not_lt_of_ge (hG v hvG)) (hm v hvPrime hvDiv)

theorem source_long_prime_no_group434
    (G : Finset ℕ) (p : ℕ) (W : ℝ)
    (hG : ∀ v ∈ G, (v:ℝ) ≤ W) (hp : p.Prime) (hPW : W < (p:ℝ)) :
    ∀ v ∈ p.primeFactors, v ∉ G := by
  intro v hv hvG
  obtain ⟨hvPrime,hvDiv,_⟩ := Nat.mem_primeFactors.mp hv
  have hvp : v = p := (Nat.prime_dvd_prime_iff_eq hvPrime hp).mp hvDiv
  subst v
  exact (not_lt_of_ge (hG p hvG)) hPW

/-- The missing inverse representation: every positive Cartesian source
quadruple with rough outside factors reconstructs its ACTUAL ordered
source index. Quotient reconstruction is exact, including repeated
residual primes and prime powers. -/
theorem source_peeled_quad_cartesian_inverse434
    (G S primeSlot : Finset ℕ) (m ps p r : ℕ)
    (hm : 0 < m) (hr : 0 < r)
    (hps : ps ∈ S) (hpsPrime : ps.Prime)
    (hpSlot : p ∈ primeSlot) (hpPrime : p.Prime)
    (hSG : S ⊆ G)
    (hmNo : ∀ v ∈ m.primeFactors, v ∉ G)
    (hpNo : ∀ v ∈ p.primeFactors, v ∉ G) :
    ((m,ps),(p,r)) ∈ sourcePeeledQuadIndices G S primeSlot (m*ps*p*r) := by
  classical
  have hpsPos : 0 < ps := hpsPrime.pos
  have hpPos : 0 < p := hpPrime.pos
  let n := m*ps*p*r
  have hn : 0 < n := by dsimp [n]; positivity
  have hpsAll : ps.primeFactors ⊆ G := by
    intro v hv
    obtain ⟨hvPrime,hvDiv,_⟩ := Nat.mem_primeFactors.mp hv
    have heq : v = ps := (Nat.prime_dvd_prime_iff_eq hvPrime hpsPrime).mp hvDiv
    simpa [heq] using hSG hps
  have hOutside : sourceOutsidePart G n = m*p*sourceOutsidePart G r :=
    source_outside_part_fourfactor_exact G m ps p r
      (Nat.ne_of_gt hm) hpsPrime.ne_zero hpPrime.ne_zero (Nat.ne_of_gt hr)
      hmNo hpNo hpsAll
  have hOutsidePos : sourceOutsidePart G n ≠ 0 := by
    intro hz
    have hparts := sourceParts_mul G n (Nat.ne_of_gt hn)
    rw [hz] at hparts
    simp only [zero_mul] at hparts
    exact (Nat.ne_of_gt hn) hparts.symm
  have hMP : m*p ∣ sourceOutsidePart G n := by
    rw [hOutside]
    exact dvd_mul_right _ _
  have hM : m ∈ (sourceOutsidePart G n).divisors :=
    Nat.mem_divisors.mpr ⟨(dvd_mul_right m p).trans hMP,hOutsidePos⟩
  have hP : p ∈ (sourceOutsidePart G n).divisors :=
    Nat.mem_divisors.mpr ⟨(dvd_mul_left p m).trans hMP,hOutsidePos⟩
  have hPs : ps ∈ smallPrimeSupport S n := by
    apply Finset.mem_filter.mpr
    refine ⟨hps,?_⟩
    change ps ∣ m*ps*p*r
    exact ((dvd_mul_left ps m).trans (dvd_mul_right (m*ps) p)).trans
      (dvd_mul_right (m*ps*p) r)
  have ht : ((m,p),ps) ∈ sourcePeeledTripleIndices G S primeSlot n := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hM,hP⟩,hPs⟩,hpSlot,hpPrime,hMP⟩
  have hq : n/(m*ps*p) = r := by
    dsimp [n]
    exact Nat.mul_div_cancel_left r (by positivity)
  apply Finset.mem_image.mpr
  refine ⟨((m,p),ps),ht,?_⟩
  change ((m,ps),(p,n/(m*ps*p))) = ((m,ps),(p,r))
  rw [hq]

/-- Source-faithful inverse: free-of-group conditions are derived from
the original roughness of alpha and the actual long prime exceeding
all marked primes. These inequalities are scale obligations, not
unproved cancellation estimates. -/
theorem source_original_quad_inverse_from_source_support434
    (G S primeSlot : Finset ℕ) (alpha : ℕ → ℂ)
    (m ps p r : ℕ) (W : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hAlpha : alpha m ≠ 0)
    (hRough : ∀ v, alpha v ≠ 0 → SourceRoughAbove v W)
    (hG : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hps : ps ∈ S) (hpsPrime : ps.Prime)
    (hpSlot : p ∈ primeSlot) (hpPrime : p.Prime)
    (hLong : W < (p:ℝ)) (hSG : S ⊆ G) :
    ((m,ps),(p,r)) ∈ sourcePeeledQuadIndices G S primeSlot (m*ps*p*r) :=
  source_peeled_quad_cartesian_inverse434 G S primeSlot m ps p r
    hm hr hps hpsPrime hpSlot hpPrime hSG
    (source_rough_alpha_no_group434 G m W hG (hRough m hAlpha))
    (source_long_prime_no_group434 G p W hG hpPrime hLong)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGlobalCartesian -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

abbrev SourceQuad434 := ((ℕ × ℕ) × (ℕ × ℕ))
def sourceQuadProduct434 (z : SourceQuad434) : ℕ :=
  z.1.1*z.1.2*z.2.1*z.2.2

/-- Independent supports; the source long slot retains its primality test.
The product cutoff is kept in the summand, rather than discarded. -/
noncomputable def sourceIndependentQuadSupport434
    (N : ℕ) (S primeSlot : Finset ℕ) : Finset SourceQuad434 :=
  ((Finset.Icc 1 N).product S).product
    ((primeSlot.filter Nat.Prime).product (Finset.Icc 1 N))

theorem source_actual_quad_in_independent_support434
    (G S primeSlot : Finset ℕ) (N n : ℕ)
    (hn : n ∈ Finset.Icc 1 N) (hSG : S ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (z : SourceQuad434) (hz : z ∈ sourcePeeledQuadIndices G S primeSlot n) :
    z ∈ sourceIndependentQuadSupport434 N S primeSlot ∧
      sourceQuadProduct434 z = n := by
  classical
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hprod := source_peeled_quad_product_exact G S primeSlot n hnpos hSG hSPrime z hz
  have hm : 0 < z.1.1 := by
    by_contra h
    have hz0 : z.1.1 = 0 := by omega
    simp only [hz0, zero_mul] at hprod
    omega
  have hr : 0 < z.2.2 := by
    by_contra h
    have hz0 : z.2.2 = 0 := by omega
    simp only [hz0, mul_zero] at hprod
    omega
  have hs : 0 < z.1.2 := by
    by_contra h
    have hz0 : z.1.2 = 0 := by omega
    simp only [hz0, mul_zero, zero_mul] at hprod
    omega
  have hp : 0 < z.2.1 := by
    by_contra h
    have hz0 : z.2.1 = 0 := by omega
    simp only [hz0, mul_zero, zero_mul] at hprod
    omega
  have hmDiv : z.1.1 ∣ n := by
    rw [← hprod]
    exact ⟨z.1.2*z.2.1*z.2.2, by ring⟩
  have hrDiv : z.2.2 ∣ n := by
    rw [← hprod]
    exact ⟨z.1.1*z.1.2*z.2.1, by ring⟩
  have hmN : z.1.1 ≤ N := (Nat.le_of_dvd hnpos hmDiv).trans (Finset.mem_Icc.mp hn).2
  have hrN : z.2.2 ≤ N := (Nat.le_of_dvd hnpos hrDiv).trans (Finset.mem_Icc.mp hn).2
  obtain ⟨t,ht,henc⟩ := Finset.mem_image.mp hz
  have hsource := Finset.mem_filter.mp ht
  have hsmall := (Finset.mem_product.mp hsource.1).2
  have hslot := hsource.2.1
  have hprime := hsource.2.2.1
  have hpsS : z.1.2 ∈ S := by
    rw [← henc]
    exact (Finset.mem_filter.mp hsmall).1
  have hpSlot : z.2.1 ∈ primeSlot := by
    rw [← henc]
    exact hslot
  have hpPrime : z.2.1.Prime := by
    rw [← henc]
    exact hprime
  refine ⟨?_, hprod⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm,hmN⟩,hpsS⟩,
      Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpSlot,hpPrime⟩,
          Finset.mem_Icc.mpr ⟨hr,hrN⟩⟩⟩

/-- Equality of the genuine source fibre and the independent Cartesian
product fibre, on the exact nonzero alpha support. -/
theorem source_original_cartesian_fibre434
    (G S primeSlot : Finset ℕ) (N n : ℕ) (alpha : ℕ → ℂ) (W : ℝ)
    (hn : n ∈ Finset.Icc 1 N)
    (hSG : S ⊆ G) (hSPrime : ∀ v ∈ S, v.Prime)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (hG : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hLong : ∀ p ∈ primeSlot, W < (p:ℝ)) :
    (sourcePeeledQuadIndices G S primeSlot n).filter
      (fun z => alpha z.1.1 ≠ 0) =
    (sourceIndependentQuadSupport434 N S primeSlot).filter
      (fun z => sourceQuadProduct434 z = n ∧ alpha z.1.1 ≠ 0) := by
  classical
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz,ha⟩
    obtain ⟨hc,hp⟩ := source_actual_quad_in_independent_support434
      G S primeSlot N n hn hSG hSPrime z hz
    exact ⟨hc,hp,ha⟩
  · rintro ⟨hc,hprod,ha⟩
    have hc' := Finset.mem_product.mp hc
    have hmps := Finset.mem_product.mp hc'.1
    have hpr := Finset.mem_product.mp hc'.2
    have hm := (Finset.mem_Icc.mp hmps.1).1
    have hr := (Finset.mem_Icc.mp hpr.2).1
    have hp := Finset.mem_filter.mp hpr.1
    have hinv := source_original_quad_inverse_from_source_support434
      G S primeSlot alpha z.1.1 z.1.2 z.2.1 z.2.2 W
      hm hr ha hRough hG hmps.2 (hSPrime _ hmps.2)
      hp.1 hp.2 (hLong _ hp.1) hSG
    change sourceQuadProduct434 z = n at hprod
    rw [show z.1.1*z.1.2*z.2.1*z.2.2 = n from hprod] at hinv
    exact ⟨hinv,ha⟩

/-- GLOBAL source occurrence equality, after summing over every original
integer and occurrence. Any weight (including the actual smooth size
cutoff, additive phase, and Mellin twist) is retained at the exact
product. No energy estimate or bijection hypothesis is assumed. -/
theorem source_original_global_cartesian_sum434
    (G S primeSlot : Finset ℕ) (N : ℕ) (alpha : ℕ → ℂ) (W : ℝ)
    (hSG : S ⊆ G) (hSPrime : ∀ v ∈ S, v.Prime)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (hG : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hLong : ∀ p ∈ primeSlot, W < (p:ℝ))
    (weight : ℕ → ℂ) (term : SourceQuad434 → ℂ)
    (hzero : ∀ z, alpha z.1.1 = 0 → term z = 0) :
    (∑ n ∈ Finset.Icc 1 N, weight n *
        ∑ z ∈ sourcePeeledQuadIndices G S primeSlot n, term z) =
    ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
      if sourceQuadProduct434 z ∈ Finset.Icc 1 N then
        weight (sourceQuadProduct434 z) * term z else 0 := by
  classical
  have hfibre (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (∑ z ∈ sourcePeeledQuadIndices G S primeSlot n, term z) =
      ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
        if sourceQuadProduct434 z = n then term z else 0 := by
    calc
      _ = ∑ z ∈ (sourcePeeledQuadIndices G S primeSlot n).filter
          (fun z => alpha z.1.1 ≠ 0), term z := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases ha : alpha z.1.1 = 0
        · simp [ha,hzero z ha]
        · simp [ha]
      _ = ∑ z ∈ (sourceIndependentQuadSupport434 N S primeSlot).filter
          (fun z => sourceQuadProduct434 z = n ∧ alpha z.1.1 ≠ 0), term z := by
        rw [source_original_cartesian_fibre434 G S primeSlot N n alpha W
          hn hSG hSPrime hRough hG hLong]
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases ha : alpha z.1.1 = 0
        · simp [ha,hzero z ha]
        · simp [ha]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
          if sourceQuadProduct434 z = n then weight n * term z else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfibre n hn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp
    _ = ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
        ∑ n ∈ Finset.Icc 1 N,
          if sourceQuadProduct434 z = n then weight n * term z else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [eq_comm]
      by_cases hp : sourceQuadProduct434 z ∈ Finset.Icc 1 N
      · simp [hp]
      · simp [hp]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcCorrelationTarget -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open scoped BigOperators
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/- Frozen literal sh:arc-target conclusion. This is a target predicate,
not a proved theorem or an axiom. The eventual uniform source hypotheses
and choice of discrepancy exponent must still be discharged. Lambda is
the source smooth size cutoff and power twist, not an arbitrary energy input.
The unchanged final goal remains Green64.green_64. -/
def SourceOriginalArcConclusion434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (Lambda : ℕ → ℂ) (L Y Hprime Carc A K : ℝ)
    (h den : ℕ) : Prop :=
  (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
    ‖sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
      ts tb b k primeSlot Ptwist alpha c chi sigma0 sigma1 Lambda
      (((h:ℝ)/(den:ℝ)+(beta:ℝ) : ℝ) : AddCircle (1:ℝ))‖^2) ≤ K*Y*L^(-A)

/- Exact quantitative sh:correlation conclusion for actual endpoint
sequences U=F W_ell epsilon, V=G W_ell epsilon. This predicate does
not certify that arbitrary U,V satisfy source admissibility. k is integer,
and positivity of BOTH endpoints is retained. Finite cutoff N must be
derived from compact support of psi. No 2u+1 endpoint is substituted. -/
def SourceOriginalCorrelationConclusion434
    (N : ℕ) (U V : ℕ → ℂ) (psi : ℝ → ℂ)
    (Z L a1 a2 D K : ℝ) (k : ℤ) : Prop :=
  ‖∑ n ∈ Finset.Icc 1 N,
    if 0 < (n:ℤ)+k then
      psi ((n:ℝ)/Z) * ((n:ℂ)⁻¹) *
        sourceUnitTwist n a1 * sourceUnitTwist ((n:ℤ)+k).toNat a2 *
        star (U n) * V ((n:ℤ)+k).toNat
    else 0‖ ≤ K*L^(-D)

/-- Literal physical GLOBAL equality: all n and original occurrences
become independent Cartesian supports. Every gcd class, character,
marked residual, source twist, and the true 1/Vs are unchanged. -/
theorem source_original_global_grouped_cartesian434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
    (W : ℝ) (hSG : S ⊆ G) (hSPrime : ∀ v ∈ S, v.Prime)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (hGroup : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hLong : ∀ p ∈ primeSlot, W < (p:ℝ))
    (weight : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, weight n *
      sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
        n den h hden) =
    ∑ d : {d : ℕ // d ∈ den.divisors},
      ∑ xi : DirichletCharacter ℂ (den/(d:ℕ)),
        ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
          if sourceQuadProduct434 z ∈ Finset.Icc 1 N then
            weight (sourceQuadProduct434 z) *
              (if Nat.gcd z.2.2 den = (d:ℕ) then
                sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
          den h hden d xi z else 0)
          else 0 := by
  classical
  unfold sourcePeeledGroupedPhysicalSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi hxi
  simpa only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero] using
    source_original_global_cartesian_sum434 G S primeSlot N alpha W
      hSG hSPrime hRough hGroup hLong weight
      (fun z => if Nat.gcd z.2.2 den = (d:ℕ) then
        sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
          den h hden d xi z else 0)
      (by
        intro z ha
        by_cases hg : Nat.gcd z.2.2 den = (d:ℕ)
        · simp [hg,sourcePeeledFixedGcdCharacterTerm,ha]
        · simp [hg])

/-- The same literal GLOBAL expression now uses genuine independent
four-coordinate boxes, intersected with original supports. The product
cutoff remains in the summand and is not replaced by a box cutoff. -/
theorem source_original_global_grouped_cartesian_boxes434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
    (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
    (W : ℝ) (hSG : S ⊆ G) (hSPrime : ∀ v ∈ S, v.Prime)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (hGroup : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hLong : ∀ p ∈ primeSlot, W < (p:ℝ))
    (weight : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, weight n *
      sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
        n den h hden) =
    ∑ d : {d : ℕ // d ∈ den.divisors},
      ∑ xi : DirichletCharacter ℂ (den/(d:ℕ)),
        ∑ j ∈ (sourceIndependentQuadSupport434 N S primeSlot).image
            sourceQuadDyadIndex434,
          ∑ z ∈ (((Finset.Icc 1 N) ∩ sourceDyad434 j.1.1).product
                (S ∩ sourceDyad434 j.1.2)).product
              (((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1).product
                ((Finset.Icc 1 N) ∩ sourceDyad434 j.2.2)),
            if sourceQuadProduct434 z ∈ Finset.Icc 1 N then
              weight (sourceQuadProduct434 z) *
                (if Nat.gcd z.2.2 den = (d:ℕ) then
                  sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
          den h hden d xi z else 0)
            else 0 := by
  classical
  rw [source_original_global_grouped_cartesian434 G Parity S primeSlot
    Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
    N den h hden W hSG hSPrime hRough hGroup hLong weight]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro xi hxi
  rw [source_canonical_dyad_sum434]
  apply Finset.sum_congr rfl
  intro j hj
  have hbox := source_cartesian_dyad_fibre434
    (Finset.Icc 1 N) S (primeSlot.filter Nat.Prime) (Finset.Icc 1 N) j
    (fun n hn => (Finset.mem_Icc.mp hn).1)
    (fun n hn => (hSPrime n hn).pos)
    (fun n hn => (Finset.mem_filter.mp hn).2.pos)
    (fun n hn => (Finset.mem_Icc.mp hn).1)
  change (∑ z ∈ ((sourceIndependentQuadSupport434 N S primeSlot).filter
    (fun z => sourceQuadDyadIndex434 z = j)), _) = _
  rw [show (sourceIndependentQuadSupport434 N S primeSlot).filter
      (fun z => sourceQuadDyadIndex434 z = j) = _ from hbox]

/-- Original additive phase, including the factor 2*pi and the actual
rational denominator. This is not a Mellin phase. -/
theorem source_original_additive_center_phase434 (n den h : ℕ) (beta : ℝ) :
    fourier (T:=1) (n:ℤ)
      (((h:ℝ)/(den:ℝ)+(beta:ℝ) : ℝ):AddCircle (1:ℝ)) =
    sourceRationalPhase den h n *
      fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ)) := by
  simp only [fourier_coe_apply,sourceRationalPhase,div_one]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Literal cutoff-weighted peeled endpoint evaluated at the original
rational center becomes the GLOBAL independent Cartesian sum. The
joint rational character factors, real small normalization and physical
residual are all the original term, not an assumed box polynomial. -/
theorem source_original_weighted_peeled_global_cartesian434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Parity : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
       ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Parity ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L a tau C : ℝ) (den h : ℕ) (hden : 0 < den)
    (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (tau*L))
    (hRough : ∀ m, alpha m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (tau*L) ≤ (p:ℝ))
    (hGroupRough : ∀ v ∈ G, (v:ℝ) ≤ Real.exp (Real.sqrt L))
    (hLongRough : Real.exp (Real.sqrt L) < Real.exp (tau*L))
    (Lambda : ℕ → ℂ) (beta : ℝ) :
    sourceWeightedPeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
      ts tb b k primeSlot Parity alpha c chi0 sigma0 sigma1 Lambda
      (((h:ℝ)/(den:ℝ)+(beta:ℝ) : ℝ):AddCircle (1:ℝ)) =
    ∑ d : {d : ℕ // d ∈ den.divisors},
      ∑ xi : DirichletCharacter ℂ (den/(d:ℕ)),
        ∑ z ∈ sourceIndependentQuadSupport434 N S primeSlot,
          if sourceQuadProduct434 z ∈ Finset.Icc 1 N then
            (Lambda (sourceQuadProduct434 z) *
              fourier (T:=1) ((sourceQuadProduct434 z):ℤ)
                (beta:AddCircle (1:ℝ))) *
              (if Nat.gcd z.2.2 den = (d:ℕ) then
                sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb
                  q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
                  den h hden d xi z else 0)
          else 0 := by
  classical
  have hSG : S ⊆ G := by
    intro v hv
    rw [hG]
    simp [hv]
  have hLP : ∀ p ∈ primeSlot, Real.exp (Real.sqrt L) < (p:ℝ) :=
    fun p hp => hLongRough.trans_le (hSlotRange p hp)
  have hEval :
      sourceWeightedPeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot Parity alpha c chi0 sigma0 sigma1 Lambda
        (((h:ℝ)/(den:ℝ)+(beta:ℝ) : ℝ):AddCircle (1:ℝ)) =
      ∑ n ∈ Finset.Icc 1 N,
        (Lambda n * fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ))) *
        (sourceRationalPhase den h n *
          fourierCoeff (T:=1)
            (sourcePeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k primeSlot Parity alpha c chi0 sigma0 sigma1) (n:ℤ)) := by
    simp only [sourceWeightedPeeledMarkedFourier,source_nat_fourier_literal]
    apply Finset.sum_congr rfl
    intro n hn
    have hc := source_peeled_fourier_coefficient_exact
      N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Parity alpha c chi0 sigma0 sigma1 n
    rw [if_pos hn] at hc
    rw [hc, source_original_additive_center_phase434]
    ring
  rw [hEval]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        (Lambda n * fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ))) *
        sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
          n den h hden := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [source_original_fourier_grouped_physical_exact N qBase S Ts Tb
        q0 Vs Vsmall Vbig ts tb b k primeSlot Parity alpha c chi0 sigma0 sigma1
        G hG hParityG hSPrime hTsPrime hTbPrime L a tau C n den h hden
        hdenCap hW hsmall hlong hRough hSRange hSlotRange,if_pos hn]
    _ = _ := source_original_global_grouped_cartesian434 G Parity S primeSlot
      Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
      N den h hden (Real.exp (Real.sqrt L)) hSG hSPrime hRough hGroupRough hLP
      (fun n => Lambda n * fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ)))

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalBox -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

noncomputable def sourceOriginalRationalCoefficient434
    (den h : ℕ) (hden : 0 < den) (d : {d : ℕ // d ∈ den.divisors})
    (xi : DirichletCharacter ℂ (den/(d:ℕ))) : ℂ :=
  letI : NeZero (den/(d:ℕ)) :=
    ⟨Nat.ne_of_gt (source_divisor_quotient_pos den d.1 hden d.2)⟩
  sourceCharacterCoefficient (den/(d:ℕ)) h xi

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (den h : ℕ) (hden : 0 < den)
  (d : {d : ℕ // d ∈ den.divisors})
  (xi : DirichletCharacter ℂ (den/(d:ℕ)))

/-- Exact physical term, including the genuine joint character and 1/Vs.
The gcd test is already in the literal marked residual. Roughness is
used only on nonzero alpha support. No energy premise enters. -/
theorem source_original_physical_reciprocal_term434
    (W : ℝ) (hBase : 0 < qBase)
    (hModW : ((qBase*den:ℕ):ℝ) ≤ W)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (z : SourceQuad434) (hz : 0 < z.1.1 ∧ 0 < z.1.2 ∧
      0 < z.2.1 ∧ 0 < z.2.2) (t : ℝ) :
    ((sourceQuadProduct434 z:ℂ)⁻¹ * sourcePhase (sourceQuadProduct434 z) t) *
      (if Nat.gcd z.2.2 den = (d:ℕ) then
        sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb q0 Vs Vsmall Vbig
          ts tb b k qBase alpha c chi0 sigma0 sigma1 den h hden d xi z
       else 0) =
    sourceOriginalRationalCoefficient434 den h hden d xi *
      sourceActualFourDyadLiteralTerm alpha
        (fun ps => ((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps * xi ps)
        (fun p => xi p)
        (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig ts tb b k
          G Parity c den d.1 (den/(d:ℕ)) xi 0)
        (sourceJointCharacter qBase (den/(d:ℕ)) chi0 xi) sigma0 sigma1 t z := by
  classical
  letI : NeZero (den/(d:ℕ)) := ⟨Nat.ne_of_gt (source_divisor_quotient_pos den d.1 hden d.2)⟩
  by_cases ha : alpha z.1.1 = 0
  · simp [sourcePeeledFixedGcdCharacterTerm,sourceActualFourDyadLiteralTerm,ha]
  have hq : 0 < den/(d:ℕ) := source_divisor_quotient_pos den d.1 hden d.2
  have hmod : 0 < qBase*(den/(d:ℕ)) := Nat.mul_pos hBase hq
  have hmodW : ((qBase*(den/(d:ℕ)):ℕ):ℝ) ≤ W := by
    have hn : qBase*(den/(d:ℕ)) ≤ qBase*den :=
      Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    have hnR : ((qBase*(den/(d:ℕ)):ℕ):ℝ) ≤ ((qBase*den:ℕ):ℝ) := by exact_mod_cast hn
    exact hnR.trans hModW
  have hc : IsCoprime (z.1.1:ℤ) (qBase*(den/(d:ℕ))) :=
    Nat.isCoprime_iff_coprime.mpr
      (rough_factor_coprime z.1.1 _ W hmod hmodW (hRough _ ha))
  have hchar := source_joint_character_source_unit_exact
    qBase (den/(d:ℕ)) chi0 xi (z.1.1:ℤ) hc
  have hphase : sourcePhase (sourceQuadProduct434 z) t =
      sourcePhase z.1.1 t * sourcePhase z.1.2 t *
        sourcePhase z.2.1 t * sourcePhase z.2.2 t := by
    simp only [sourceQuadProduct434]
    rw [sourcePhase_mul _ _ (Nat.mul_pos (Nat.mul_pos hz.1 hz.2.1) hz.2.2.1) hz.2.2.2,
      sourcePhase_mul _ _ (Nat.mul_pos hz.1 hz.2.1) hz.2.2.1,
      sourcePhase_mul _ _ hz.1 hz.2.1]
  have hinv : (sourceQuadProduct434 z:ℂ)⁻¹ =
      (z.1.1:ℂ)⁻¹ * (z.1.2:ℂ)⁻¹ * (z.2.1:ℂ)⁻¹ * (z.2.2:ℂ)⁻¹ := by
    simp only [sourceQuadProduct434,Nat.cast_mul,mul_inv_rev]
    ring
  by_cases hg : Nat.gcd z.2.2 den = (d:ℕ)
  · simp only [if_pos hg,sourceOriginalRationalCoefficient434,sourcePeeledFixedGcdCharacterTerm,
      sourceActualFourDyadLiteralTerm]
    rw [hphase,hinv]
    rw [sourcePhase_add z.1.1 sigma0 t,sourcePhase_add z.2.1 sigma1 t]
    simp only [← source_actual_unit_twist_as_phase]
    rw [show sourceJointCharacter qBase (den/(d:ℕ)) chi0 xi z.1.1 =
        chi0 z.1.1 * xi z.1.1 by simpa using hchar]
    ring
  · simp [hg,sourceActualFourDyadLiteralTerm,sourcePhysicalMarkedResidual]

/-- A genuine independent physical box is exactly the previously checked
smooth fourfold polynomial, with its original gcd/character coefficient. -/
theorem source_original_physical_box_smooth_exact434
    (W : ℝ) (hBase : 0 < qBase)
    (hModW : ((qBase*den:ℕ):ℝ) ≤ W)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (small long R : Finset ℕ) (a bnd : ℕ) (cutoff : ℕ → ℂ)
    (ha : 1 ≤ a) (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p) (hr : ∀ r ∈ R, 0 < r) (t : ℝ) :
    (∑ z ∈ ((Finset.Icc a bnd).product small).product (long.product R),
      cutoff (sourceQuadProduct434 z) *
        ((sourceQuadProduct434 z:ℂ)⁻¹ * sourcePhase (sourceQuadProduct434 z) t) *
        (if Nat.gcd z.2.2 den = (d:ℕ) then
          sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k qBase alpha c chi0 sigma0 sigma1 den h hden d xi z
         else 0)) =
    sourceOriginalRationalCoefficient434 den h hden d xi *
      sourceActualSmoothFourDyadAt small long R a bnd cutoff alpha
        (fun ps => ((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps * xi ps)
        (fun p => xi p)
        (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig ts tb b k
          G Parity c den d.1 (den/(d:ℕ)) xi 0)
        (sourceJointCharacter qBase (den/(d:ℕ)) chi0 xi) sigma0 sigma1 t := by
  classical
  simp only [sourceActualSmoothFourDyadAt,sourceActualFourDyadTuples,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hz
  obtain ⟨hm,hps⟩ := Finset.mem_product.mp hms
  obtain ⟨hpl,hrr⟩ := Finset.mem_product.mp hpr
  have hzpos : 0 < z.1.1 ∧ 0 < z.1.2 ∧ 0 < z.2.1 ∧ 0 < z.2.2 :=
    ⟨by have := (Finset.mem_Icc.mp hm).1; omega,hs _ hps,hp _ hpl,hr _ hrr⟩
  have hterm := source_original_physical_reciprocal_term434 G Parity S Ts Tb
    q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
    den h hden d xi W hBase hModW hRough z hzpos t
  change _ = sourceOriginalRationalCoefficient434 den h hden d xi * (cutoff (sourceQuadProduct434 z) * _)
  calc
    _ = cutoff (sourceQuadProduct434 z) *
        (((sourceQuadProduct434 z:ℂ)⁻¹ * sourcePhase (sourceQuadProduct434 z) t) *
          (if Nat.gcd z.2.2 den = (d:ℕ) then
            sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k qBase alpha c chi0 sigma0 sigma1 den h hden d xi z
           else 0)) := by ring
    _ = _ := by rw [hterm]; ring

end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGlobalPhysicalTerminal -/

section

open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/-- Scalar normalization is extracted from the SMALL coefficient only;
the marked residual retains its original Vs and every other parameter. -/
theorem source_original_smooth_small_scalar434
    (small long R : Finset ℕ) (a b : ℕ)
    (cutoff alpha bs bp residual : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t : ℝ) (v : ℂ) :
    sourceActualSmoothFourDyadAt small long R a b cutoff alpha
      (fun p => v * bs p) bp residual chi sigma0 sigma1 t =
    v * sourceActualSmoothFourDyadAt small long R a b cutoff alpha
      bs bp residual chi sigma0 sigma1 t := by
  classical
  unfold sourceActualSmoothFourDyadAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [sourceActualFourDyadLiteralTerm]
  ring

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- The actual normalized physical endpoint polynomial, before any
estimate. All original integer occurrences and the smooth product
cutoff remain present. For the original cutoff this is P_a(t)/Y. -/
noncomputable def sourceOriginalPhysicalMellin434
    (cutoff : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (cutoff n * ((n:ℂ)⁻¹ * sourcePhase n t)) *
      sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
        n den h hden

noncomputable def sourceOriginalNormalizedBox434
    (cutoff : ℕ → ℂ)
    (d : {d : ℕ // d ∈ den.divisors})
    (xi : DirichletCharacter ℂ (den/(d:ℕ)))
    (j : Green64Analytic.CorrelationMellin.SourceQuad434) (t : ℝ) : ℂ :=
  sourceActualSmoothFourDyadAt
    (S ∩ sourceDyad434 j.1.2)
    ((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1)
    ((Finset.Icc 1 N) ∩ sourceDyad434 j.2.2)
    (2^j.1.1) (min N (2^(j.1.1+1)-1)) cutoff alpha
    (fun ps => literalSourceParity Parity ps * xi ps)
    (fun p => xi p)
    (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig ts tb coef k
      G Parity c den d.1 (den/(d:ℕ)) xi 0)
    (sourceJointCharacter qBase (den/(d:ℕ)) chi0 xi) sigma0 sigma1 t

/-- Exact GLOBAL endpoint-to-smooth-box equality. Half-open canonical
dyads are used, hence every original occurrence appears exactly once.
The compact cutoff, all gcd classes, all characters, and true 1/Vs
survive the identity. No box or endpoint energy premise is assumed. -/
theorem source_original_global_physical_mellin_exact434
    (W : ℝ) (hBase : 0 < qBase)
    (hModW : ((qBase*den:ℕ):ℝ) ≤ W)
    (hSG : S ⊆ G) (hSPrime : ∀ v ∈ S, v.Prime)
    (hRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m W)
    (hGroup : ∀ v ∈ G, (v:ℝ) ≤ W)
    (hLong : ∀ p ∈ primeSlot, W < (p:ℝ))
    (cutoff : ℕ → ℂ) (hCut : ∀ n, N < n → cutoff n = 0) (t : ℝ) :
    sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      N den h hden cutoff t =
    ((1/Vs:ℝ):ℂ) *
      ∑ d : {d : ℕ // d ∈ den.divisors},
        ∑ xi : DirichletCharacter ℂ (den/(d:ℕ)),
          ∑ j ∈ (sourceIndependentQuadSupport434 N S primeSlot).image
              sourceQuadDyadIndex434,
            sourceOriginalRationalCoefficient434 den h hden d xi *
              sourceOriginalNormalizedBox434 G Parity S primeSlot Ts Tb
                q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
                sigma0 sigma1 N den cutoff d xi j t := by
  classical
  unfold sourceOriginalPhysicalMellin434
  rw [source_original_global_grouped_cartesian_boxes434 G Parity S primeSlot
    Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
    N den h hden W hSG hSPrime hRough hGroup hLong
    (fun n => cutoff n * ((n:ℂ)⁻¹ * sourcePhase n t))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro xi hxi
  apply Finset.sum_congr rfl
  intro j hj
  have hM := source_alpha_interval_dyad_intersection434 1 N j.1.1
  have hPow : 1 ≤ 2^j.1.1 := Nat.one_le_pow _ _ (by norm_num)
  have hmax : max 1 (2^j.1.1) = 2^j.1.1 := max_eq_right hPow
  rw [hmax] at hM
  rw [hM]
  have hs : ∀ ps ∈ S ∩ sourceDyad434 j.1.2, 0 < ps :=
    fun ps hps => (hSPrime ps (Finset.mem_inter.mp hps).1).pos
  have hp : ∀ p ∈ (primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1, 0 < p :=
    fun p hp => (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2.pos
  have hr : ∀ r ∈ (Finset.Icc 1 N) ∩ sourceDyad434 j.2.2, 0 < r :=
    fun r hr => (Finset.mem_Icc.mp (Finset.mem_inter.mp hr).1).1
  have hRemove :
      (∑ z ∈ ((Finset.Icc (2^j.1.1) (min N (2^(j.1.1+1)-1))).product
          (S ∩ sourceDyad434 j.1.2)).product
          (((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1).product
            ((Finset.Icc 1 N) ∩ sourceDyad434 j.2.2)),
        if sourceQuadProduct434 z ∈ Finset.Icc 1 N then
          (cutoff (sourceQuadProduct434 z) *
            ((sourceQuadProduct434 z:ℂ)⁻¹ * sourcePhase (sourceQuadProduct434 z) t)) *
            (if Nat.gcd z.2.2 den = (d:ℕ) then
              sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb q0 Vs
                Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
                den h hden d xi z else 0)
        else 0) =
      ∑ z ∈ ((Finset.Icc (2^j.1.1) (min N (2^(j.1.1+1)-1))).product
          (S ∩ sourceDyad434 j.1.2)).product
          (((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1).product
            ((Finset.Icc 1 N) ∩ sourceDyad434 j.2.2)),
        cutoff (sourceQuadProduct434 z) *
          ((sourceQuadProduct434 z:ℂ)⁻¹ * sourcePhase (sourceQuadProduct434 z) t) *
            (if Nat.gcd z.2.2 den = (d:ℕ) then
              sourcePeeledFixedGcdCharacterTerm G Parity S Ts Tb q0 Vs
                Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
                den h hden d xi z else 0) := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hn : sourceQuadProduct434 z ∈ Finset.Icc 1 N
    · simp only [if_pos hn]
    · obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hz
      obtain ⟨hm,hss⟩ := Finset.mem_product.mp hms
      obtain ⟨hpl,hrr⟩ := Finset.mem_product.mp hpr
      have hmpos : 0 < z.1.1 := hPow.trans (Finset.mem_Icc.mp hm).1
      have hnpos : 0 < sourceQuadProduct434 z := by
        unfold sourceQuadProduct434
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hmpos (hs _ hss))
          (hp _ hpl)) (hr _ hrr)
      have hgt : N < sourceQuadProduct434 z := by
        simp only [Finset.mem_Icc] at hn
        omega
      simp [hn,hCut _ hgt]
  rw [hRemove,source_original_physical_box_smooth_exact434 G Parity S Ts Tb
    q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1 den h
    hden d xi W hBase hModW hRough
    (S ∩ sourceDyad434 j.1.2)
    ((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1)
    ((Finset.Icc 1 N) ∩ sourceDyad434 j.2.2)
    (2^j.1.1) (min N (2^(j.1.1+1)-1)) cutoff hPow hs hp hr t]
  have hScalar : (fun ps : ℕ => ((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps * xi ps) =
      (fun ps : ℕ => ((1/Vs:ℝ):ℂ) * (literalSourceParity Parity ps * xi ps)) := by
    funext ps
    ring
  rw [hScalar,source_original_smooth_small_scalar434]
  unfold sourceOriginalNormalizedBox434
  ring
end


abbrev SourceOriginalCharacterFamily434 (den : ℕ) :=
  Σ d : {d : ℕ // d ∈ den.divisors}, DirichletCharacter ℂ (den/(d:ℕ))

theorem source_original_actual_character_family_card434
    (den : ℕ) (hden : 0 < den) :
    Fintype.card (SourceOriginalCharacterFamily434 den) = den := by
  classical
  rw [Fintype.card_sigma]
  rw [Finset.sum_coe_sort den.divisors
    (fun d : ℕ => Fintype.card (DirichletCharacter ℂ (den/d)))]
  simpa only [Nat.card_eq_fintype_card] using
    source_original_gcd_character_count den hden

theorem source_original_rational_coefficient_norm434
    (den h : ℕ) (hden : 0 < den)
    (d : {d : ℕ // d ∈ den.divisors})
    (xi : DirichletCharacter ℂ (den/(d:ℕ))) :
    ‖sourceOriginalRationalCoefficient434 den h hden d xi‖ ≤ 1 := by
  letI : NeZero (den/(d:ℕ)) :=
    ⟨Nat.ne_of_gt (source_divisor_quotient_pos den d.1 hden d.2)⟩
  exact (source_rational_phase_fourier (den/(d:ℕ)) h 1
    (source_divisor_quotient_pos den d.1 hden d.2) (Nat.coprime_one_left _)).2 xi
end Green64Analytic.CorrelationSquare


open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/-- Source-derived GLOBAL physical saving. The assumptions describe the
actual dyadic supports and scale geometry; there is NO assumed box
energy, endpoint energy, Fourier tail, or physical Memory estimate.
The original full-window discrepancy exponent is selected once before L.
The only unclosed geometric obligations are exposed explicitly in hGeo. -/
theorem eventually_source_original_global_physical_mellin_saving434
    (aexp bexp τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime Carc : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (Nlong : Green64Analytic.CorrelationMellin.SourceQuad434 → ℝ)
        (Ilong : Green64Analytic.CorrelationMellin.SourceQuad434 → Set ℝ),
      (∀ j ∈ (sourceIndependentQuadSupport434 Ncap S primeSlot).image
          sourceQuadDyadIndex434,
        1 ≤ Nlong j ∧ Set.OrdConnected (Ilong j) ∧
        Ilong j ⊆ Set.Icc (Nlong j) (2*Nlong j) ∧
        x^τ/2 ≤ Nlong j ∧ Nlong j ≤ x^η ∧
        sourceLongPrimeSourceSupport (Nlong j) (Ilong j) =
          ((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1) ∧
        Real.exp (L^aexp) ≤ ((2*(2^j.1.2):ℕ):ℝ) ∧
        ((2^j.1.2:ℕ):ℝ) ≤ Real.exp (L^bexp) ∧
        2*L*(16*A)*((2^j.1.2:ℕ):ℝ)*L^Carc ≤ Hprime) →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc))) (2*L*Y/(Hprime/L^Carc)),
        ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1 Ncap den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      (1/Vs)^2 * (den:ℝ)^2 * (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹ := by
  classical
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_uniform_full_window_original_log_budget
      aexp bexp τ η Cχ C0 q0 vmin tmax ea ec s0 cm D s1base vexp fcut epsi
      A Cpsi Kpsi hA hCpsi hKpsi hepsi hFcut
      haexp hab hb hτ hτη hη hCχ hC0 hq0 hq1 hv
  let B : ℕ := (D+2*(epsi+1)+2+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
    5*(ec+(s1+2)+gLow+2)+10
  refine ⟨B,X0,hX0,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL Y Hprime Carc hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hc sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong Nlong Ilong hGeo psi1 hSmooth hSupport v1 hv1 hBudget hden
  let cutoff := sourceActualOriginalWindowWeight Y psi1 v1
  let alpha0 := sourceAlphaDyadicCut alpha lo hi
  let J := (sourceIndependentQuadSupport434 Ncap S primeSlot).image sourceQuadDyadIndex434
  let K := (SourceOriginalCharacterFamily434 den) × {j // j ∈ J}
  let F : K → ℝ → ℂ := fun z t =>
    sourceOriginalNormalizedBox434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k qBase alpha0 c chi0 sigma0 sigma1 Ncap den cutoff
      z.1.1 z.1.2 z.2.1 t
  let coeff : K → ℂ := fun z =>
    sourceOriginalRationalCoefficient434 den h hden z.1.1 z.1.2
  let T := 2*L*Y/(Hprime/L^Carc)
  have hCoeff : ∀ z, ‖coeff z‖ ≤ 1 := fun z =>
    source_original_rational_coefficient_norm434 den h hden z.1.1 z.1.2
  have hCont : ∀ z, Continuous (F z) := by
    intro z
    exact source_actual_smooth_fourdyad_continuous _ _ _ _ _ _ _ _ _ _ _ _ _
  have hEnergy : ∀ z, (∫ t in Set.Icc (-T) T, ‖F z t‖^2) ≤ (L^D)⁻¹ := by
    intro z
    let d := z.1.1
    let xi := z.1.2
    let j := z.2.1
    obtain ⟨hN,hIconn,hI,hNlow,hNhigh,hLongID,hPmin,hPmax,hFree⟩ := hGeo j z.2.2
    have hPower (i : ℕ) : 1 ≤ 2^i := Nat.one_le_pow _ _ (by norm_num)
    have hM : Finset.Icc (2^j.1.1) (min Ncap (2^(j.1.1+1)-1)) ⊆
        Finset.Icc (2^j.1.1) (2*(2^j.1.1)) := by
      intro m hm
      obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hm
      have hu' := hu.trans (min_le_right _ _)
      rw [pow_succ] at hu'
      exact Finset.mem_Icc.mpr ⟨hl,by omega⟩
    have hSmall : S ∩ sourceDyad434 j.1.2 ⊆
        Finset.Icc (2^j.1.2) (2*(2^j.1.2)) :=
      fun p hp => source_dyad_in_closed_containing434 _ (Finset.mem_inter.mp hp).2
    have hR : (Finset.Icc 1 Ncap) ∩ sourceDyad434 j.2.2 ⊆
        Finset.Icc (2^j.2.2) (2*(2^j.2.2)) :=
      fun p hp => source_dyad_in_closed_containing434 _ (Finset.mem_inter.mp hp).2
    have hSmallPrime : ∀ p ∈ S ∩ sourceDyad434 j.1.2, p.Prime :=
      fun p hp => hSPrime p (Finset.mem_inter.mp hp).1
    have hBs : ∀ p ∈ S ∩ sourceDyad434 j.1.2,
        ‖literalSourceParity Parity p * xi p‖ ≤ 1 := by
      intro p hp
      rw [norm_mul,literal_source_parity_norm_one,one_mul]
      exact xi.norm_le_one _
    have hqpos := source_divisor_quotient_pos den d.1 hden d.2
    have hqCap : ((den/(d:ℕ):ℕ):ℝ) ≤ L^Cχ := by
      exact (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans hDenChar
    have hbcap : ((min Ncap (2^(j.1.1+1)-1):ℕ):ℝ) ≤ x^2 :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans hNcap
    have hBound := hMainL x hx hLog hL
      (2^j.1.2) (2^j.1.1) (2^j.2.2) Y Hprime Carc (Nlong j) (Ilong j)
      (hPower _) (hPower _) (hPower _) hY hYmax hH hN hIconn hI
      hNlow hNhigh hPmin hPmax hFree hYstrong hSmallGroups hBigGroups
      lo hi (2^j.1.1) (min Ncap (2^(j.1.1+1)-1)) alpha
      (hPower _) hbcap hM hAlpha hDisc
      (S ∩ sourceDyad434 j.1.2) ((Finset.Icc 1 Ncap) ∩ sourceDyad434 j.2.2)
      (fun p => literalSourceParity Parity p * xi p)
      hSmallPrime hSmall hBs hR
      (den/(d:ℕ)) xi hqpos hqCap
      qBase den d.1 chi0 xi hBaseCap hDenCap d.2 sigma0 sigma1 hSigma0 hSigma1
      C hC hCBudget S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc den d.1 (den/(d:ℕ)) xi 0 psi1 hSmooth hSupport v1 hv1 hBudget
    simpa only [F,sourceOriginalNormalizedBox434,cutoff,alpha0,T,hLongID] using hBound
  have hSum := source_original_finite_family_energy F coeff (-T) T ((L^D)⁻¹)
    hCoeff hCont hEnergy
  have hKcard : Fintype.card K = den*J.card := by
    simp only [K,Fintype.card_prod,source_original_actual_character_family_card434 den hden,
      Fintype.card_coe]
  have hJcard : J.card ≤ (Ncap.log2+1)^4 := by
    apply source_original_four_dyadic_assignment_card434
    intro z hz
    obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hz
    obtain ⟨hm,hs⟩ := Finset.mem_product.mp hms
    obtain ⟨hp,hr⟩ := Finset.mem_product.mp hpr
    obtain ⟨hmpos,hmN⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hrpos,hrN⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hpslot,hpprime⟩ := Finset.mem_filter.mp hp
    exact ⟨hmpos,hmN,(hSPrime _ hs).pos,hSN _ hs,
      hpprime.pos,hPN _ hpslot,hrpos,hrN⟩
  have hCut : ∀ n, Ncap < n → cutoff n = 0 := by
    intro n hn
    by_contra hz
    have hWin := source_actual_original_window_weight_support Y A psi1 v1
      (by linarith) hA hSupport n hz
    have hcast : (Ncap:ℝ) < (n:ℝ) := Nat.cast_lt.mpr hn
    linarith [hWin.2]
  have hEqual (t : ℝ) :
      sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha0 c chi0 sigma0 sigma1
        Ncap den h hden cutoff t = ((1/Vs:ℝ):ℂ) * ∑ z : K, coeff z * F z t := by
    rw [source_original_global_physical_mellin_exact434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha0 c chi0 sigma0 sigma1
      Ncap den h hden W hBase hModW hSG hSPrime hRough hGroup hLong cutoff hCut t]
    apply congrArg (fun a : ℂ => ((1/Vs:ℝ):ℂ) * a)
    simp only [K,Fintype.sum_prod_type,Fintype.sum_sigma,F,coeff]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro xi hxi
    exact (Finset.sum_coe_sort J (fun j =>
      sourceOriginalRationalCoefficient434 den h hden d xi *
        sourceOriginalNormalizedBox434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k qBase alpha0 c chi0 sigma0 sigma1 Ncap den cutoff d xi j t)).symm
  have hIntegral :
      (∫ t in Set.Icc (-T) T,
        ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha0 c chi0 sigma0 sigma1
          Ncap den h hden cutoff t‖^2) =
      (1/Vs)^2 * ∫ t in Set.Icc (-T) T, ‖∑ z : K, coeff z * F z t‖^2 := by
    simp_rw [hEqual,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [integral_const_mul]
  change (∫ t in Set.Icc (-T) T,
    ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha0 c chi0 sigma0 sigma1
      Ncap den h hden cutoff t‖^2) ≤ _
  rw [hIntegral]
  calc
    _ ≤ (1/Vs)^2 * (Fintype.card K:ℝ)^2 * (L^D)⁻¹ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hSum (sq_nonneg (1/Vs))
    _ = (1/Vs)^2 * (den:ℝ)^2 * (J.card:ℝ)^2 * (L^D)⁻¹ := by
      rw [hKcard,Nat.cast_mul,mul_pow]
      ring
    _ ≤ _ := by
      gcongr
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCollar -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- Literal physical coefficient at the rational center, with the original
    smooth cutoff and twist. Grouped sum retains all actual divisor and
    principal/imprimitive character families and the real 1/Vs. -/
noncomputable def sourceOriginalPhysicalEndpointCoefficient434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (n : ℕ) : ℂ :=
  psi1 ((n:ℝ)/Y) * sourcePhase n v1 *
    sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      n den h hden

/-- Exact bridge to the VERIFIED physical Mellin polynomial. The
    cutoff is unchanged and the normalization is precisely 1/Y. -/
theorem source_original_physical_endpoint_mellin_normalization434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 t : ℝ) (hY : 0 < Y) :
    (∑ n ∈ Finset.Icc 1 N,
      sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
        den h hden Y psi1 v1 n * sourcePhase n t) =
    (Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      N den h hden (sourceActualOriginalWindowWeight Y psi1 v1) t := by
  classical
  unfold sourceOriginalPhysicalMellin434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hY0 : (Y:ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  simp only [sourceOriginalPhysicalEndpointCoefficient434,sourceActualOriginalWindowWeight,
    Complex.ofReal_div,Complex.ofReal_natCast]
  field_simp

/-- True compact support of the actual coefficient follows from psi1,
    independently of marks, rational center and character family. -/
theorem source_original_physical_endpoint_support434
    (Y A : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (hY : 0 < Y)
    (hSupport : ∀ u, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (n : ℕ)
    (hn : sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      den h hden Y psi1 v1 n ≠ 0) : Y/A ≤ (n:ℝ) ∧ (n:ℝ) ≤ A*Y := by
  have hp : psi1 ((n:ℝ)/Y) ≠ 0 := by
    intro hp
    exact hn (by simp [sourceOriginalPhysicalEndpointCoefficient434,hp])
  obtain ⟨hl,hu⟩ := hSupport _ hp
  have hl' := (le_div_iff₀ hY).mp hl
  have hu' := (div_le_iff₀ hY).mp hu
  constructor
  · simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hl'
  · exact hu'

/-- NEW physical source collar ERROR, with exact actual coefficients.
    No hHigh/hLow/hTail, box energy, moment or Memory premise. -/
theorem source_original_physical_collar_error434
    (Y H A M δ : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (K : ℝ → ℂ)
    (hK : Continuous K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hH : 1 ≤ H) (hY : 0 < Y) (hA : 0 < A) (hHcap : H ≤ Y/(8*A))
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|) :
    (H^2)⁻¹ * (∫ v in Set.Icc (Y/(2*A)) (2*A*Y),
      ‖∑ n ∈ Finset.Icc 1 N,
        sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
          den h hden Y psi1 v1 n * sourceCollarKernelDifference434 K H n v‖^2) ≤
    4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2 *
      ∑ n ∈ Finset.Icc 1 N,
        ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
          den h hden Y psi1 v1 n‖^2 := by
  exact source_physical_collar_replacement_error434 (Finset.Icc 1 N) _ K M δ H Y A
    (fun n hn => (Finset.mem_Icc.mp hn).1) hK hM hδ hδ1 hH hY hA hHcap hSupport hLip

open scoped FourierTransform SchwartzMap RealInnerProductSpace

/-- Exact source logarithmic collar in Bochner form. The Fourier
frequency is 2*pi*xi*v/H, and no energy or tail is assumed. -/
theorem source_collar_log_bochner434
    (F : Finset ℕ) (a : ℕ → ℂ) (K : 𝓢(ℝ,ℂ)) (H v : ℝ)
    (hv : 0 < v) (hF : ∀ n ∈ F, 0 < n) :
    (∑ n ∈ F, a n * K (v*Real.log ((n:ℝ)/v)/H)) =
      ∫ ξ : ℝ, (𝓕 K) ξ *
        Complex.exp (((-2*Real.pi*ξ*v/H*Real.log v:ℝ):ℂ)*Complex.I) *
        (∑ n ∈ F, a n * sourcePhase n (2*Real.pi*ξ*v/H)) := by
  classical
  let E : ℝ → ℂ := fun ξ =>
    Complex.exp (((-2*Real.pi*ξ*v/H*Real.log v:ℝ):ℂ)*Complex.I)
  have hInv (u : ℝ) : K u =
      ∫ ξ : ℝ, Complex.exp (((2*Real.pi*⟪ξ,u⟫:ℝ):ℂ)*Complex.I) * (𝓕 K) ξ := by
    calc
      _ = (𝓕⁻ (𝓕 K : 𝓢(ℝ,ℂ))) u :=
        (congrArg (fun f : 𝓢(ℝ,ℂ) => f u) (FourierTransform.fourierInv_fourier_eq K)).symm
      _ = _ := by
        rw [SchwartzMap.fourierInv_coe]
        exact Real.fourierInv_eq' ((𝓕 K : 𝓢(ℝ,ℂ)) : ℝ → ℂ) u
  have hPhase (n : ℕ) (hn : n ∈ F) (ξ : ℝ) :
      Complex.exp (((2*Real.pi*⟪ξ,v*Real.log ((n:ℝ)/v)/H⟫:ℝ):ℂ)*Complex.I) =
        E ξ * sourcePhase n (2*Real.pi*ξ*v/H) := by
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hF n hn))
    unfold E sourcePhase
    rw [Real.inner_apply, Real.log_div hn0 hv.ne', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hTerm (n : ℕ) : Integrable (fun ξ : ℝ =>
      (𝓕 K) ξ * E ξ * (a n * sourcePhase n (2*Real.pi*ξ*v/H))) := by
    have hC : Continuous (fun ξ : ℝ =>
        (𝓕 K) ξ * E ξ * (a n * sourcePhase n (2*Real.pi*ξ*v/H))) := by
      unfold E sourcePhase
      fun_prop
    have hInt : Integrable (fun ξ : ℝ => (𝓕 K) ξ * a n) :=
      (𝓕 K).integrable.mul_const (a n)
    apply hInt.mono hC.aestronglyMeasurable
    filter_upwards with ξ
    simp only [norm_mul, E, Complex.norm_exp_ofReal_mul_I, sourcePhase_norm, mul_one]
    exact le_rfl
  change _ = ∫ ξ : ℝ, (𝓕 K) ξ * E ξ *
    (∑ n ∈ F, a n * sourcePhase n (2*Real.pi*ξ*v/H))
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum F (fun n _ => hTerm n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hInv, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hPhase n hn ξ]
  ring

/-- The logarithmic collar contains the literal normalized physical
polynomial, not an artificial box or Fourier-energy input. -/
theorem source_original_physical_log_collar_bochner434
    (Y H v : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (K : 𝓢(ℝ,ℂ))
    (hY : 0 < Y) (hv : 0 < v) :
    (∑ n ∈ Finset.Icc 1 N,
      sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
        den h hden Y psi1 v1 n * K (v*Real.log ((n:ℝ)/v)/H)) =
    ∫ ξ : ℝ, (𝓕 K) ξ *
      Complex.exp (((-2*Real.pi*ξ*v/H*Real.log v:ℝ):ℂ)*Complex.I) *
      ((Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
        N den h hden (sourceActualOriginalWindowWeight Y psi1 v1)
        (2*Real.pi*ξ*v/H)) := by
  rw [source_collar_log_bochner434 (Finset.Icc 1 N) _ K H v hv
    (fun n hn => (Finset.mem_Icc.mp hn).1)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [source_original_physical_endpoint_mellin_normalization434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
    alpha c chi0 sigma0 sigma1 N den h hden Y psi1 v1
    (2*Real.pi*ξ*v/H) hY]

/-- Real-time harmonic-row bound applied directly to all actual grouped
endpoint coefficients. No hTail, hHigh or hLow premise occurs. -/
theorem source_original_physical_endpoint_harmonic_row434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 t0 t1 : ℝ) (ht : t0 ≤ t1) :
    (∫ t in Set.Icc t0 t1,
      ‖∑ n ∈ Finset.Icc 1 N,
        sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
          den h hden Y psi1 v1 n * sourcePhase n t‖^2) ≤
      ((t1-t0)+16*(N:ℝ)*(1+Real.log N)) *
        ∑ n ∈ Finset.Icc 1 N,
          ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
            q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
            den h hden Y psi1 v1 n‖^2 := by
  have hMV := Green64Analytic.Correlation.continuousMeanSquare N (Finset.Icc 1 N)
    (sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      den h hden Y psi1 v1) t0 t1 (Finset.Subset.refl _) ht
  simpa only [sourcePhase, mul_comm] using hMV
end

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
  (Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ)

local notation "aPhys" => sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
  q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1

/-- The full original physical sequence has a harmonic row at its actual
support scale M, independently of the possibly much larger bookkeeping
cutoff N. No second-moment, energy or tail estimate is assumed. -/
theorem source_original_physical_endpoint_localized_row434
    (A : ℝ) (M : ℕ) (hY : 0 < Y)
    (hSupport : ∀ u, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hCut : A*Y ≤ (M:ℝ))
    (t0 t1 : ℝ) (ht : t0 ≤ t1) :
    (∫ t in Set.Icc t0 t1,
      ‖∑ n ∈ Finset.Icc 1 N, aPhys n * sourcePhase n t‖^2) ≤
      ((t1-t0)+16*(M:ℝ)*(1+Real.log M)) *
        ∑ n ∈ Finset.Icc 1 N, ‖aPhys n‖^2 := by
  classical
  let F := (Finset.Icc 1 N).filter (fun n => n ≤ M)
  have hsub : F ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hzero (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (hNot : n ∉ F) : aPhys n = 0 := by
    by_contra hNZ
    have hu := (source_original_physical_endpoint_support434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
      den h hden Y A psi1 v1 hY hSupport n hNZ).2
    have hnM : n ≤ M := by exact_mod_cast hu.trans hCut
    exact hNot (Finset.mem_filter.mpr ⟨hn,hnM⟩)
  have hP (t : ℝ) :
      (∑ n ∈ Finset.Icc 1 N, aPhys n * sourcePhase n t) =
        ∑ n ∈ F, aPhys n * sourcePhase n t := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hNot
    rw [hzero n hn hNot,zero_mul]
  have hE : (∑ n ∈ F, ‖aPhys n‖^2) ≤ ∑ n ∈ Finset.Icc 1 N, ‖aPhys n‖^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
  have hFM : F ⊆ Finset.Icc 1 M := by
    intro n hn
    obtain ⟨hnN,hnM⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnN).1,hnM⟩
  have hR : 0 ≤ (t1-t0)+16*(M:ℝ)*(1+Real.log M) := by
    by_cases hM : M = 0
    · simp [hM,sub_nonneg.mpr ht]
    · have hm : 1 ≤ (M:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM)
      have hl := Real.log_nonneg hm
      have hd : 0 ≤ t1-t0 := sub_nonneg.mpr ht
      positivity
  have hMV := Green64Analytic.Correlation.continuousMeanSquare M F aPhys t0 t1 hFM ht
  calc
    _ = ∫ t in Set.Icc t0 t1, ‖∑ n ∈ F, aPhys n * sourcePhase n t‖^2 := by
      simp_rw [hP]
    _ ≤ ((t1-t0)+16*(M:ℝ)*(1+Real.log M)) * ∑ n ∈ F, ‖aPhys n‖^2 := by
      simpa only [sourcePhase,mul_comm] using hMV
    _ ≤ _ := mul_le_mul_of_nonneg_left hE hR
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLinearCollarSupport -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1300000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- For every original marked source coefficient: the ordinary
additive collar sum with kernel K((n-v)/H) has no leakage outside
the REAL original v window. Includes zeros of the original cutoff;
no replacement or arbitrary coefficient is introduced. -/
theorem source_original_linear_collar_zero_outside434
    (Y A H δ : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ)
    (K : ℝ → ℂ) (hA : 1 ≤ A)
    (hY : 0 < Y) (hH : 0 < H) (hHcap : H ≤ Y/(8*A))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hSupportPsi : ∀ u, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hSupportK : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (v : ℝ) (hv : v ∉ Set.Icc (Y/(2*A)) (2*A*Y)) :
    (∑ n ∈ Finset.Icc 1 N,
      sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
        sigma0 sigma1 den h hden Y psi1 v1 n *
          K (((n:ℝ)-v)/H)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  let a : ℂ := sourceOriginalPhysicalEndpointCoefficient434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
    k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1 n
  by_cases hzero : a = 0
  · simp only [a] at hzero
    simp [hzero]
  · have hBounds :
        Y/A ≤ (n:ℝ) ∧ (n:ℝ) ≤ A*Y :=
      source_original_physical_endpoint_support434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
        coef k qBase alpha c chi0 sigma0 sigma1 den h hden
        Y A psi1 v1 hY hSupportPsi n hzero
    have hKzero := source_linear_collar_true_window_support434
      K (n:ℝ) v Y A H δ hA hY hH hHcap hδ hδ1
      hSupportK hBounds.1 hBounds.2 hv
    simp [hKzero]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLiteralTerminal -/

section

open Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- Real interval corresponding to the source's disjoint NATURAL dyad.
The upper endpoint is 2^(j+1)-1, rather than 2^(j+1). -/
def sourceOriginalLongInterval434 (I : Set ℝ) (j : ℕ) : Set ℝ :=
  I ∩ Set.Icc ((2^j : ℕ) : ℝ) ((2^(j+1)-1 : ℕ) : ℝ)

theorem source_original_long_interval_geometry434
    (I : Set ℝ) (j : ℕ) (hI : Set.OrdConnected I) :
    Set.OrdConnected (sourceOriginalLongInterval434 I j) ∧
      sourceOriginalLongInterval434 I j ⊆
        Set.Icc ((2^j : ℕ) : ℝ) (2*((2^j : ℕ) : ℝ)) := by
  refine ⟨hI.inter Set.ordConnected_Icc, ?_⟩
  intro p hp
  obtain ⟨hlo,hhi⟩ := hp.2
  refine ⟨hlo,hhi.trans ?_⟩
  have hn : 2^(j+1)-1 ≤ 2*(2^j : ℕ) := by
    rw [pow_succ]
    omega
  exact_mod_cast hn

/-- The original interval and primality test remain literal after cutting.
This statement does not enlarge the original long-prime support. -/
theorem source_original_long_interval_support434
    (primeSlot : Finset ℕ) (I : Set ℝ) (j : ℕ)
    (hSlot : ∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) :
    sourceLongPrimeSourceSupport ((2^j : ℕ):ℝ)
        (sourceOriginalLongInterval434 I j) =
      (primeSlot.filter Nat.Prime) ∩ sourceDyad434 j := by
  classical
  ext p
  have hpw : 0 < 2^(j+1 : ℕ) := Nat.pow_pos (by norm_num)
  have hfloor : ⌊2*((2^j : ℕ):ℝ)⌋₊ = 2*(2^j : ℕ) := by
    rw [show 2*((2^j : ℕ):ℝ) = ((2*(2^j : ℕ):ℕ):ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  simp only [sourceLongPrimeSourceSupport,Finset.mem_filter,
    Finset.mem_range,Finset.mem_inter,sourceDyad434,Finset.mem_Ico,
    sourceOriginalLongInterval434,Set.mem_inter_iff,Set.mem_Icc,hfloor,hSlot]
  constructor
  · rintro ⟨⟨hcap,hprime⟩,hIp,hlo,hhi⟩
    have hln : 2^j ≤ p := by exact_mod_cast hlo
    have hun : p ≤ 2^(j+1)-1 := by exact_mod_cast hhi
    exact ⟨⟨⟨hprime,hIp⟩,hprime⟩,hln,by omega⟩
  · rintro ⟨⟨⟨hprime,hIp⟩,_⟩,hlo,hhi⟩
    have hun : p ≤ 2^(j+1)-1 := by omega
    refine ⟨⟨?_,hprime⟩,hIp,?_,?_⟩
    · rw [pow_succ] at hhi
      omega
    · exact_mod_cast hlo
    · exact_mod_cast hun

/-- Every retained index has a genuine source tuple. Its original small
and long primes imply ALL dyadic band inequalities. -/
theorem source_original_retained_dyad_bands434
    (Ncap : ℕ) (S primeSlot : Finset ℕ) (I : Set ℝ)
    (smallLo smallHi longLo longHi : ℝ)
    (hSPrime : ∀ s ∈ S, s.Prime)
    (hSmall : ∀ s ∈ S, smallLo ≤ (s:ℝ) ∧ (s:ℝ) ≤ smallHi)
    (hSlot : ∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I)
    (hLong : I ⊆ Set.Icc longLo longHi)
    (j : Green64Analytic.CorrelationMellin.SourceQuad434)
    (hj : j ∈ (sourceIndependentQuadSupport434 Ncap S primeSlot).image
      sourceQuadDyadIndex434) :
    smallLo ≤ ((2*(2^j.1.2) : ℕ):ℝ) ∧
      ((2^j.1.2 : ℕ):ℝ) ≤ smallHi ∧
      longLo/2 ≤ ((2^j.2.1 : ℕ):ℝ) ∧
      ((2^j.2.1 : ℕ):ℝ) ≤ longHi := by
  classical
  obtain ⟨z,hz,hjz⟩ := Finset.mem_image.mp hj
  change z ∈ ((Finset.Icc 1 Ncap).product S).product
    ((primeSlot.filter Nat.Prime).product (Finset.Icc 1 Ncap)) at hz
  obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hz
  obtain ⟨hm,hs⟩ := Finset.mem_product.mp hms
  obtain ⟨hp,hr⟩ := Finset.mem_product.mp hpr
  have hsp := hSPrime _ hs
  have hpp := (Finset.mem_filter.mp hp).2
  have hsdyad : z.1.2 ∈ sourceDyad434 j.1.2 := by
    rw [← hjz]
    exact source_positive_in_canonical_dyad434 _ hsp.pos
  have hpdyad : z.2.1 ∈ sourceDyad434 j.2.1 := by
    rw [← hjz]
    exact source_positive_in_canonical_dyad434 _ hpp.pos
  obtain ⟨hsl,hsu⟩ := hSmall _ hs
  have hplp := ((hSlot _).mp (Finset.mem_filter.mp hp).1).2
  obtain ⟨hpl,hpu⟩ := hLong hplp
  have hsr := source_dyad_in_closed_containing434 _ hsdyad
  have hpr := source_dyad_in_closed_containing434 _ hpdyad
  obtain ⟨hsslo,hsshi⟩ := Finset.mem_Icc.mp hsr
  obtain ⟨hpplo,hpphi⟩ := Finset.mem_Icc.mp hpr
  have hssloR : ((2^j.1.2:ℕ):ℝ) ≤ (z.1.2:ℝ) := by exact_mod_cast hsslo
  have hsshiR : (z.1.2:ℝ) ≤ ((2*(2^j.1.2):ℕ):ℝ) := by exact_mod_cast hsshi
  have hpploR : ((2^j.2.1:ℕ):ℝ) ≤ (z.2.1:ℝ) := by exact_mod_cast hpplo
  have hpphiR : (z.2.1:ℝ) ≤ 2*((2^j.2.1:ℕ):ℝ) := by exact_mod_cast hpphi
  exact ⟨hsl.trans hsshiR,hssloR.trans hsu,by linarith,hpploR.trans hpu⟩

/-- Uniform hGeo DERIVED from literal source bands, exact interval
membership, and the actual two nonempty width-at-most-one free cells.
There is no assumed box energy, tail, discrepancy or physical Memory. -/
theorem eventually_source_original_literal_hGeo434
    (aexp bexp cexp Carc A : ℝ)
    (hbc : bexp < cexp) (hc : 0 < cexp) (hA : 1 ≤ A) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (x τ η Hprime : ℝ) (Ncap : ℕ) (S primeSlot : Finset ℕ) (I : Set ℝ),
    Set.OrdConnected I →
    (∀ s ∈ S, s.Prime) →
    (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
    (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
    I ⊆ Set.Icc (x^τ) (x^η) →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
      (F1 : Finset ι₁) (F2 : Finset ι₂) (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ)
      (U1 U2 : ℝ),
    F1.Nonempty → F2.Nonempty →
    (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
    (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
    (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
    0 < U1 → 0 < U2 →
    Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
    Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
    Hprime = U1*U2 →
    ∀ j ∈ (sourceIndependentQuadSupport434 Ncap S primeSlot).image sourceQuadDyadIndex434,
      1 ≤ ((2^j.2.1:ℕ):ℝ) ∧
      Set.OrdConnected (sourceOriginalLongInterval434 I j.2.1) ∧
      sourceOriginalLongInterval434 I j.2.1 ⊆
        Set.Icc ((2^j.2.1:ℕ):ℝ) (2*((2^j.2.1:ℕ):ℝ)) ∧
      x^τ/2 ≤ ((2^j.2.1:ℕ):ℝ) ∧
      ((2^j.2.1:ℕ):ℝ) ≤ x^η ∧
      sourceLongPrimeSourceSupport ((2^j.2.1:ℕ):ℝ)
        (sourceOriginalLongInterval434 I j.2.1) =
        ((primeSlot.filter Nat.Prime) ∩ sourceDyad434 j.2.1) ∧
      Real.exp (L^aexp) ≤ ((2*(2^j.1.2):ℕ):ℝ) ∧
      ((2^j.1.2:ℕ):ℝ) ≤ Real.exp (L^bexp) ∧
      2*L*(16*A)*((2^j.1.2:ℕ):ℝ)*L^Carc ≤ Hprime := by
  filter_upwards [eventually_source_actual_original_free_scale
    bexp cexp (16*A) Carc 2 hbc hc (by linarith) (by norm_num)] with L hFree
  intro x τ η Hprime Ncap S primeSlot I hI hSPrime hSmall hSlot hLong
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hH j hj
  have hLower1 := source_original_nonempty_cell_lower F1 p1 U1 (L^cexp)
    hF1 hp1 hmin1 hU1 hcell1
  have hLower2 := source_original_nonempty_cell_lower F2 p2 U2 (L^cexp)
    hF2 hp2 hmin2 hU2 hcell2
  have hHlower : Real.exp (2*L^cexp-2) ≤ Hprime := by
    rw [hH,show 2*L^cexp-2 = (L^cexp-1)+(L^cexp-1) by ring,Real.exp_add]
    exact mul_le_mul hLower1 hLower2 (Real.exp_pos _).le hU1.le
  obtain ⟨hPmin,hPmax,hNmin,hNmax⟩ :=
    source_original_retained_dyad_bands434 Ncap S primeSlot I
      (Real.exp (L^aexp)) (Real.exp (L^bexp)) (x^τ) (x^η)
      hSPrime hSmall hSlot hLong j hj
  obtain ⟨hconn,hsubset⟩ := source_original_long_interval_geometry434 I j.2.1 hI
  have hOne : 1 ≤ ((2^j.2.1:ℕ):ℝ) := by
    exact_mod_cast (Nat.one_le_pow j.2.1 2 (by norm_num))
  exact ⟨hOne,hconn,hsubset,hNmin,hNmax,
    source_original_long_interval_support434 primeSlot I j.2.1 hSlot,
    hPmin,hPmax,hFree (2^j.1.2) Hprime hPmax hHlower⟩
end Green64Analytic.CorrelationSquare

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/-- Global saving for the actual physical Mellin endpoint. Its hGeo
premise is removed: literal source prime bands, original interval
membership and nonempty source comparison cells imply it. This is a
Mellin statement; it does not assert the additive sh:arc-target. -/
theorem eventually_source_original_global_physical_from_literal_cells434
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc))) (2*L*Y/(Hprime/L^Carc)),
        ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1 Ncap den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      (1/Vs)^2 * (den:ℝ)^2 * (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹ := by
  have hc : 0 < cexp := lt_trans haexp (lt_trans hab hbc)
  obtain ⟨B,X0,hX0,hMain⟩ :=
    eventually_source_original_global_physical_mellin_saving434
      aexp bexp τ η Cχ C0 q0 vmin tmax ea ec s0 cm D s1base vexp fcut epsi
      A Cpsi Kpsi hA hCpsi hKpsi hepsi hFcut
      haexp hab hb hτ hτη hη hCχ hC0 hq0 hq1 hv
  refine ⟨B,X0,hX0,?_⟩
  filter_upwards [hMain,eventually_source_original_literal_hGeo434
    aexp bexp cexp Carc A hbc hc hA] with L hMainL hGeoL
  intro x hx hLog hL Y Hprime hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget hden
  have hGeo := hGeoL x τ η Hprime Ncap S primeSlot I hI hSPrime
    hSmall hSlot hIBand F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  exact hMainL x hx hLog hL Y Hprime Carc hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong
    (fun j => ((2^j.2.1:ℕ):ℝ))
    (fun j => sourceOriginalLongInterval434 I j.2.1) hGeo
    psi1 hSmooth hSupport v1 hv1 hBudget hden
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCollarTerminal -/

section

open scoped BigOperators FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- Angular real-time inversion of the true logarithmic collar, with the
Jacobian H/(2*pi*v) derived rather than assumed. -/
theorem source_collar_log_real_time434
    (F : Finset ℕ) (a : ℕ → ℂ) (K : 𝓢(ℝ,ℂ)) (H v : ℝ)
    (hH : 0 < H) (hv : 0 < v) (hF : ∀ n ∈ F, 0 < n) :
    (∑ n ∈ F, a n * K (v*Real.log ((n:ℝ)/v)/H)) =
      ((H/(2*Real.pi*v):ℝ):ℂ) *
        ∫ t : ℝ, (𝓕 K) (H*t/(2*Real.pi*v)) *
          Complex.exp (((-t*Real.log v:ℝ):ℂ)*Complex.I) *
          (∑ n ∈ F, a n * sourcePhase n t) := by
  rw [source_collar_log_bochner434 F a K H v hv hF]
  let k : ℝ := 2*Real.pi*v/H
  let ρ : ℝ := H/(2*Real.pi*v)
  let g : ℝ → ℂ := fun t =>
    (𝓕 K) (ρ*t) *
      Complex.exp (((-t*Real.log v:ℝ):ℂ)*Complex.I) *
      (∑ n ∈ F, a n * sourcePhase n t)
  have hk : 0 < k := by dsimp [k]; positivity
  have hρk : ρ*k = 1 := by
    dsimp [ρ,k]
    field_simp
  have hInv : k⁻¹ = ρ := by
    have hDiv : ρ = 1/k := (eq_div_iff hk.ne').mpr hρk
    simpa only [one_div] using hDiv.symm
  have hSub : (∫ ξ : ℝ, (𝓕 K) ξ *
      Complex.exp (((-2*Real.pi*ξ*v/H*Real.log v:ℝ):ℂ)*Complex.I) *
      (∑ n ∈ F, a n * sourcePhase n (2*Real.pi*ξ*v/H))) =
      ∫ ξ : ℝ, g (k*ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    have hρ : ρ*(k*ξ) = ξ := by rw [← mul_assoc,hρk,one_mul]
    have hfreq : k*ξ = 2*Real.pi*ξ*v/H := by dsimp [k]; ring
    simp only [g]
    rw [hρ,hfreq]
    rw [show -2*Real.pi*ξ*v/H*Real.log v =
      -(2*Real.pi*ξ*v/H)*Real.log v by ring]
  rw [hSub,Measure.integral_comp_mul_left g k,hInv,abs_of_pos (by dsimp [ρ]; positivity)]
  change (ρ:ℂ) * (∫ t : ℝ, g t) = _
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [g,ρ]
  congr 2
  congr 1
  ring

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- The literal original physical collar, expressed at real Mellin time.
All marks, character/gcd families and 1/Vs remain in the same source coefficient. -/
theorem source_original_physical_collar_real_time434
    (Y H v : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (K : 𝓢(ℝ,ℂ))
    (hY : 0 < Y) (hH : 0 < H) (hv : 0 < v) :
    (∑ n ∈ Finset.Icc 1 N,
      sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
        den h hden Y psi1 v1 n * K (v*Real.log ((n:ℝ)/v)/H)) =
    ((H/(2*Real.pi*v):ℝ):ℂ) *
      ∫ t : ℝ, (𝓕 K) (H*t/(2*Real.pi*v)) *
        Complex.exp (((-t*Real.log v:ℝ):ℂ)*Complex.I) *
        ((Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0 sigma1
          N den h hden (sourceActualOriginalWindowWeight Y psi1 v1) t) := by
  rw [source_collar_log_real_time434 (Finset.Icc 1 N) _ K H v hH hv
    (fun n hn => (Finset.mem_Icc.mp hn).1)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [source_original_physical_endpoint_mellin_normalization434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
    alpha c chi0 sigma0 sigma1 N den h hden Y psi1 v1 t hY]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalNamedMellin -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators FourierTransform
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1800000

/-- Definitionally exact, including source's original n=0 convention. -/
theorem source_literal_phase_eq_original434 (n : ℕ) (t : ℝ) :
    sourceLiteralMellinPhase434 n t = sourcePhase n t := rfl

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
  (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
/-- The actual FROZEN source physical marked-coefficient polynomial
is precisely Y times sourceOriginalPhysicalMellin434, including the
original smooth cutoff, rational gcd, Dirichlet character, parity and
all small/big-mark multiplicities. No substituted coefficient. -/
theorem source_original_literal_mellin_identification434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 t : ℝ) (hY : 0 < Y) :
    sourceLiteralFiniteMellin434 (Finset.Icc 1 N)
      (sourceOriginalPhysicalEndpointCoefficient434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1) t =
    (Y:ℂ) * sourceOriginalPhysicalMellin434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
      alpha c chi0 sigma0 sigma1 N den h hden
      (sourceActualOriginalWindowWeight Y psi1 v1) t := by
  have hsource := source_original_physical_endpoint_mellin_normalization434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
    alpha c chi0 sigma0 sigma1 N den h hden Y psi1 v1 t hY
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        sourceOriginalPhysicalEndpointCoefficient434
          G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1 n *
          sourcePhase n t := by
      unfold sourceLiteralFiniteMellin434
      apply Finset.sum_congr rfl
      intro n hn
      rw [source_literal_phase_eq_original434]
    _ = _ := hsource
/-- Including the original common physical factor exp(-it log Y). -/
theorem source_original_twisted_mellin_identification434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 t : ℝ) (hY : 0 < Y) :
    sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N)
      (sourceOriginalPhysicalEndpointCoefficient434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1) t =
    Complex.exp (((-t*Real.log Y:ℝ):ℂ)*Complex.I) *
      ((Y:ℂ) * sourceOriginalPhysicalMellin434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t) := by
  unfold sourceLiteralTwistedMellin434
  rw [source_original_literal_mellin_identification434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
    alpha c chi0 sigma0 sigma1 N den h hden Y psi1 v1 t hY]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLowMellinContinuity -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1200000

/-- True SOURCE physical Mellin (not an L² surrogate) is continuous:
the already-certified literal coefficient identity identifies Y*M(t)
with a finite actual marked-coefficient Dirichlet polynomial. -/
theorem source_original_physical_mellin_continuous434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
    (Y : ℝ) (hY : 0 < Y) (psi1 : ℝ → ℂ) (v1 : ℝ) :
    Continuous (fun t : ℝ =>
      sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c
        chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t) := by
  let a : ℕ → ℂ :=
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
      k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hEq : (fun t : ℝ =>
      sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c
        chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t) =
      (fun t : ℝ =>
        (Y:ℂ)⁻¹ * sourceLiteralFiniteMellin434
          (Finset.Icc 1 N) a t) := by
    funext t
    have hSource :=
      source_original_literal_mellin_identification434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
        coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
        Y psi1 v1 t hY
    rw [hSource]
    field_simp
  rw [hEq]
  exact continuous_const.mul
    (source_literal_finite_mellin_continuous434 (Finset.Icc 1 N) a)
end Green64Analytic.CorrelationSquare

end

