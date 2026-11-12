module

public import Green64.Library.Weights.Part041
public import Green64.Library.Weights.Part039
public import Mathlib.Data.Nat.Factorization.Basic
public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part012
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part032
public import Green64.Library.Weights.Part020
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part016
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part017

@[expose] public section

/-!
# Weights / Part042

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePeelingEnergyTriangle -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Quantitative Fourier energy triangle inequality on each literal
real beta arc. All three Fourier maps live on the normalized unit
circle but are integrated against real Lebesgue beta. -/
theorem source_beta_arc_add_energy_le
    (f g : C(AddCircle (1:ℝ),ℂ))
    (center H : ℝ) (hH : 2 ≤ H) :
    (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖(f+g) ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
      2 * (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖f ((center+beta) : AddCircle (1:ℝ))‖^2) +
      2 * (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖g ((center+beta) : AddCircle (1:ℝ))‖^2) := by
  let S : Set ℝ := {beta : ℝ | |beta| ≤ 1/H}
  have hS : S = Set.Icc (-(1/H)) (1/H) := by
    ext beta
    simp only [S,Set.mem_setOf_eq,Set.mem_Icc,abs_le]
  have hCompact : IsCompact S := by
    rw [hS]
    exact isCompact_Icc
  let x : ℝ → AddCircle (1:ℝ) := fun beta => ((center+beta) : AddCircle (1:ℝ))
  have hContinuousX : Continuous x :=
    (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_const.add continuous_id)
  have hContf : Continuous (fun beta : ℝ => ‖f (x beta)‖^2) :=
    ((continuous_norm.comp (f.continuous.comp hContinuousX)).pow 2)
  have hContg : Continuous (fun beta : ℝ => ‖g (x beta)‖^2) :=
    ((continuous_norm.comp (g.continuous.comp hContinuousX)).pow 2)
  have hContsum : Continuous (fun beta : ℝ => ‖(f+g) (x beta)‖^2) :=
    ((continuous_norm.comp ((f+g).continuous.comp hContinuousX)).pow 2)
  have hIntf : IntegrableOn (fun beta : ℝ => ‖f (x beta)‖^2) S :=
    hContf.continuousOn.integrableOn_compact hCompact
  have hIntg : IntegrableOn (fun beta : ℝ => ‖g (x beta)‖^2) S :=
    hContg.continuousOn.integrableOn_compact hCompact
  have hIntsum : IntegrableOn (fun beta : ℝ => ‖(f+g) (x beta)‖^2) S :=
    hContsum.continuousOn.integrableOn_compact hCompact
  have hIntfg : IntegrableOn
      (fun beta : ℝ => 2*‖f (x beta)‖^2+2*‖g (x beta)‖^2) S :=
    (hIntf.const_mul 2).add (hIntg.const_mul 2)
  have hPoint : ∀ beta : ℝ,
      ‖(f+g) (x beta)‖^2 ≤
        2*‖f (x beta)‖^2+2*‖g (x beta)‖^2 := by
    intro beta
    have hTr : ‖f (x beta)+g (x beta)‖ ≤
      ‖f (x beta)‖+‖g (x beta)‖ :=
       norm_add_le _ _
    have hf : 0 ≤ ‖f (x beta)‖ := norm_nonneg _
    have hg : 0 ≤ ‖g (x beta)‖ := norm_nonneg _
    have hfg : 0 ≤ ‖f (x beta)+g (x beta)‖ := norm_nonneg _
    have hDiff := sq_nonneg (‖f (x beta)‖-‖g (x beta)‖)
    simp only [ContinuousMap.add_apply]
    nlinarith
  change (∫ beta in S, ‖(f+g) (x beta)‖^2) ≤
    2*(∫ beta in S, ‖f (x beta)‖^2) +
    2*(∫ beta in S, ‖g (x beta)‖^2)
  calc
    _ ≤ ∫ beta in S,
           (2*‖f (x beta)‖^2+2*‖g (x beta)‖^2) :=
      integral_mono_ae hIntsum hIntfg
        (Filter.Eventually.of_forall hPoint)
    _ = _ := by
      rw [integral_add (hIntf.const_mul 2) (hIntg.const_mul 2)]
      simp only [integral_const_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedParity -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1500000

/-- Multiplicity parity is multiplicative without coprimality. -/
theorem source_literal_parity_mul434 (P : Finset ℕ) (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    literalSourceParity P (m*n) = literalSourceParity P m * literalSourceParity P n := by
  simp only [literalSourceParity, Nat.factorization_mul hm hn,
    Finsupp.add_apply, Finset.sum_add_distrib, pow_add]

/-- Every labelled prime in the parity group contributes one minus sign. -/
theorem source_literal_parity_prime434 (P : Finset ℕ) (p : ℕ)
    (hp : p.Prime) (hP : p ∈ P) : literalSourceParity P p = -1 := by
  simp [literalSourceParity, hp.factorization, Finsupp.single_apply, hP]

/-- The count is of SLOTS, not distinct prime values. Repeated labels are allowed. -/
theorem source_shared_product_parity434 {ι : Type} [DecidableEq ι]
    (P : Finset ℕ) (F : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ F, (p i).Prime) (hP : ∀ i ∈ F, p i ∈ P) :
    literalSourceParity P (∏ i ∈ F, p i) = (-1:ℂ)^F.card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [literalSourceParity]
  | @insert i F hi ih =>
    have hip : (p i).Prime := hp i (Finset.mem_insert_self _ _)
    have hFp : ∀ j ∈ F, (p j).Prime := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hFP : ∀ j ∈ F, p j ∈ P := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, source_literal_parity_mul434 P _ _ hip.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun j hj => (hFp j hj).ne_zero))]
    rw [source_literal_parity_prime434 P _ hip (hP i (Finset.mem_insert_self _ _)),
      ih hFp hFP, Finset.card_insert_of_notMem hi, pow_succ]
    ring

noncomputable def sourceEndpointSign434 (P : Finset ℕ) (b : Bool) (n : ℕ) : ℂ :=
  if b then literalSourceParity P n else 1

/-- Independent choices at the two ends retain a pattern-constant sign.
The same residual operator is used; its norm is not asserted invariant
under arbitrary pattern reweighting. -/
theorem source_shared_dilation_independent_signs434
    (P : Finset ℕ) (D w wp r : ℕ) (b1 b2 : Bool)
    (hD : D ≠ 0) (hw : w ≠ 0) (hwp : wp ≠ 0)
    (hSign : literalSourceParity P D = (-1:ℂ)^r) :
    sourceEndpointSign434 P b1 (D*w) * sourceEndpointSign434 P b2 (D*wp) =
      ((if b1 then (-1:ℂ)^r else 1)*(if b2 then (-1:ℂ)^r else 1)) *
        sourceEndpointSign434 P b1 w * sourceEndpointSign434 P b2 wp := by
  cases b1 <;> cases b2 <;>
    simp only [sourceEndpointSign434, Bool.false_eq_true, if_false, if_true,
      source_literal_parity_mul434 P D w hD hw,
      source_literal_parity_mul434 P D wp hD hwp, hSign] <;> ring

theorem source_shared_pattern_sign_norm434 (r : ℕ) (b1 b2 : Bool) :
    ‖(if b1 then (-1:ℂ)^r else 1)*(if b2 then (-1:ℂ)^r else 1)‖ = 1 := by
  cases b1 <;> cases b2 <;> simp [norm_mul, norm_pow]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedPrimeSupport -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 4000000

/-- A shared set retains exactly its literal prime divisors. -/
theorem source_prime_dvd_shared_product434 (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) (q : ℕ) (hq : q.Prime) :
    q ∣ ∏ p ∈ R, p ↔ q ∈ R := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [hq.not_dvd_one]
  | @insert p R hp ih =>
    have hpP := hR p (Finset.mem_insert_self p R)
    have hRP : ∀ r ∈ R, r.Prime := fun r hr => hR r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hp,hq.dvd_mul,ih hRP]
    simp only [Finset.mem_insert,Nat.prime_dvd_prime_iff_eq hq hpP]

/-- Exact support identity on a clean shared-prime fibre. -/
theorem source_shared_prime_support434 (P R : Finset ℕ) (w : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRP : R ⊆ P) :
    smallPrimeSupport P ((∏ p ∈ R, p)*w) = R ∪ smallPrimeSupport P w := by
  classical
  ext q
  by_cases hq : q ∈ P
  · simp only [smallPrimeSupport,Finset.mem_filter,hq,true_and,Finset.mem_union,
      (hP q hq).dvd_mul,source_prime_dvd_shared_product434 R
        (fun p hp => hP p (hRP hp)) q (hP q hq)]
  · have hqR : q ∉ R := fun hr => hq (hRP hr)
    simp only [smallPrimeSupport,Finset.mem_filter,hq,false_and,Finset.mem_union,hqR,or_self]

/-- The count gained at this group is the number of shared labels,
not the multiplicity count of all prime powers of w. -/
theorem source_shared_prime_count434 (P R : Finset ℕ) (w : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRP : R ⊆ P)
    (hAvoid : ∀ p ∈ R, ¬p ∣ w) :
    smallPrimeCount P ((∏ p ∈ R, p)*w) = R.card+smallPrimeCount P w := by
  classical
  unfold smallPrimeCount
  rw [source_shared_prime_support434 P R w hP hRP]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr (fun p hp hwp => hAvoid p hp (Finset.mem_filter.mp hwp).2)

/-- An unshared physical mark in a clean completion divides w itself.
The reverse direction does not require coprimality or squarefreeness of w. -/
theorem source_unshared_divisor_iff434 (P R : Finset ℕ) (w p : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hRP : R ⊆ P) (hp : p ∈ P) (hpR : p ∉ R) :
    p ∣ (∏ q ∈ R, q)*w ↔ p ∣ w := by
  rw [(hP p hp).dvd_mul,source_prime_dvd_shared_product434 R
    (fun q hq => hP q (hRP hq)) p (hP p hp)]
  simp only [hpR,false_or]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryParityChoice -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- An auxiliary prime can belong to the outside-part group set
WITHOUT being twisted: the original parity subset is independent.
The parity of p therefore depends on p ∈ Ptw, not on p ∈ G. -/
theorem source_auxiliary_prime_parity_choice434
    (Ptw : Finset ℕ) (p : ℕ) (hp : p.Prime) :
    literalSourceParity Ptw p =
      if p ∈ Ptw then (-1:ℂ) else 1 := by
  by_cases hmem : p ∈ Ptw
  · simp only [hmem,ite_true]
    exact source_literal_parity_prime434 Ptw p hp hmem
  · simp only [hmem,ite_false]
    simp [literalSourceParity,hp.factorization,Finsupp.single_apply,
      Finset.sum_ite_eq',hmem]

/-- The exact independent endpoint sign carried by auxiliary p.
No shared-twist simplification is used; eps1 and eps2 may differ. -/
theorem source_auxiliary_prime_two_sign_choices434
    (Ptw : Finset ℕ) (p y yp : ℕ)
    (eps1 eps2 : Bool) (hp : p.Prime)
    (hy : 0 < y) (hyp : 0 < yp) :
    sourceEndpointSign434 Ptw eps1 (p*y)*
      sourceEndpointSign434 Ptw eps2 (p*yp) =
    ((if eps1 then (if p ∈ Ptw then (-1:ℂ) else 1) else 1)*
      (if eps2 then (if p ∈ Ptw then (-1:ℂ) else 1) else 1))*
    sourceEndpointSign434 Ptw eps1 y*
      sourceEndpointSign434 Ptw eps2 yp := by
  let r : ℕ := if p ∈ Ptw then 1 else 0
  have hP : literalSourceParity Ptw p = (-1:ℂ)^r := by
    rw [source_auxiliary_prime_parity_choice434 Ptw p hp]
    dsimp only [r]
    split_ifs <;> simp
  have hSigns := source_shared_dilation_independent_signs434
    Ptw p y yp r eps1 eps2 hp.ne_zero hy.ne' hyp.ne' hP
  by_cases hmem : p ∈ Ptw
  · simp only [r,if_pos hmem,pow_one] at hSigns
    simpa only [if_pos hmem] using hSigns
  · simp only [r,if_neg hmem,pow_zero] at hSigns
    simpa only [if_neg hmem] using hSigns
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalEndpointGlobal -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 3500000

/-- The existing divisor-moment theorem at p=1 is the full original
endpoint bound. Neither discrepancy nor a square exception is assumed. -/
theorem source_original_endpoint_global_square434
    (G : Finset ℕ) (W Lambda epsilon : ℕ → ℂ)
    (primeSlot : Finset ℕ) (alpha c : ℕ → ℂ)
    (N q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 A C B M : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hAlpha : ∀ m, ‖alpha m‖ ≤ A) (hCseq : ∀ r, ‖c r‖ ≤ C)
    (hWeight : ∀ n ∈ Finset.Icc 1 N, ‖W n‖ ≤ B)
    (hLambda : ∀ n ∈ Finset.Icc 1 N, ‖Lambda n‖ ≤ M)
    (hSign : ∀ n ∈ Finset.Icc 1 N, ‖epsilon n‖ = 1) :
    (∑ n ∈ Finset.Icc 1 N, ‖Lambda n*epsilon n*
      sourceEndpoint (sourceOutsidePart G) W primeSlot alpha c q chi s0 s1 n‖^2) ≤
      (A*C*(M*B))^2*(N:ℝ)*(1+Real.log (N:ℝ))^16 := by
  let weight : ℕ → ℂ := fun n => Lambda n*epsilon n*W n
  have hSet : Green64Analytic.CorrelationD.squareDivisibleSupport N 1 = Finset.Icc 1 N := by
    ext n
    simp [Green64Analytic.CorrelationD.squareDivisibleSupport]
  have hStar : ∀ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N 1,
      sourceOutsidePart G n ∣ n/1^2 := by
    intro n hn
    rw [hSet] at hn
    have hParts := sourceParts_mul G n (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    simpa using (show sourceOutsidePart G n ∣ n from ⟨sourceInsidePart G n,hParts.symm⟩)
  have hW : ∀ n ∈ Green64Analytic.CorrelationD.squareDivisibleSupport N 1,
      ‖weight n‖ ≤ M*B := by
    intro n hn
    rw [hSet] at hn
    dsimp only [weight]
    rw [norm_mul,norm_mul,hSign n hn,mul_one]
    exact mul_le_mul (hLambda n hn) (hWeight n hn) (norm_nonneg _) hM
  have hMoment := sourceSquareAtPrime (sourceOutsidePart G) weight primeSlot alpha c
    N q 1 chi s0 s1 A C (M*B) hA hC (mul_nonneg hM hB) hAlpha hCseq
    (by norm_num) hStar hW
  rw [hSet] at hMoment
  simp only [one_pow,Nat.div_one] at hMoment
  convert hMoment using 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  dsimp only [sourceEndpoint,weight]
  ring

/-- A parity choice at one endpoint has unit norm independently of the
choice at the other endpoint, including multiplicities at every prime. -/
theorem source_endpoint_sign_norm434 (P : Finset ℕ) (b : Bool) (n : ℕ) :
    ‖sourceEndpointSign434 P b n‖ = 1 := by
  cases b <;> simp [sourceEndpointSign434,literal_source_parity_norm_one]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFourChannelComparison -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 4500000

noncomputable def sourceSignedCoefficients434 (P : Finset ℕ) (eps : Bool)
    (a : ℤ → ℂ) (n : ℤ) : ℂ := sourceEndpointSign434 P eps n.toNat*a n

theorem source_signed_coefficients_square434 (P : Finset ℕ) (eps : Bool)
    (a : ℤ → ℂ) (S : Finset ℤ) :
    (∑ n ∈ S, ‖sourceSignedCoefficients434 P eps a n‖^2) =
      ∑ n ∈ S, ‖a n‖^2 := by
  simp only [sourceSignedCoefficients434,norm_mul,source_endpoint_sign_norm434,one_mul]

theorem source_endpoint_sign_star434 (P : Finset ℕ) (eps : Bool) (n : ℕ) :
    star (sourceEndpointSign434 P eps n) = sourceEndpointSign434 P eps n := by
  cases eps <;> simp [sourceEndpointSign434,literalSourceParity]

/-- BOTH independent endpoint signs. Only the first endpoint requires
an arc estimate, separately for its two choices. The actual comparison
multiplier is unchanged and the removed shared-slot phase stays outside it. -/
theorem source_four_channel_comparison_saving434 {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (shift : ι → ℤ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) (Q : ℕ) (P : Finset ℕ)
    (Hprime Carc Cexp Karc Kglobal Kminor Y L D E : ℝ)
    (hL : 1 ≤ L) (hCexp : 0 ≤ Cexp) (hKarc : 0 ≤ Karc)
    (hKglobal : 0 ≤ Kglobal) (hKminor : 0 ≤ Kminor) (hY : 0 ≤ Y)
    (hMass : (∑ j ∈ J, ‖c j‖) ≤ 1)
    (hQ : (Q:ℝ) ≤ L^Cexp) (hr : 0 ≤ L^Carc/Hprime)
    (hrhalf : L^Carc/Hprime < 1/2)
    (hFirst : (∑ n ∈ S, ‖a n‖^2) ≤ Kglobal*Y*L^E)
    (hSecond : (∑ n ∈ T, ‖b n‖^2) ≤ Kglobal*Y*L^E)
    (hArc : ∀ (eps : Bool) (den h : ℕ), 0 < den → den ≤ Q → h < den →
      (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
        ‖sourceCircleFourierPoly S (sourceSignedCoefficients434 P eps a)
          (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2)
      ≤ Karc*Y*L^(-(2*Cexp+2*D+E)))
    (hMinor : ∀ θ ∉ sourceCircleRationalArcs434 Q (L^Carc/Hprime),
      ‖sourceFiniteShiftMultiplier434 J c shift θ‖ ≤ Kminor*L^(-D-E)) :
    ∀ (eps1 eps2 : Bool) (sharedSlots : ℕ),
      ‖((if eps1 then (-1:ℂ)^sharedSlots else 1)*
          (if eps2 then (-1:ℂ)^sharedSlots else 1)) *
        (∑ j ∈ J, c j*(∑ m ∈ S, ∑ n ∈ T,
          if n = m+shift j then
            star (sourceSignedCoefficients434 P eps1 a m)*
              sourceSignedCoefficients434 P eps2 b n else 0))‖ ≤
      (Real.sqrt (2*Karc*Kglobal)+Kminor*Kglobal)*Y*L^(-D) := by
  intro eps1 eps2 sharedSlots
  have hFirstSigned : (∑ n ∈ S, ‖sourceSignedCoefficients434 P eps1 a n‖^2)
      ≤ Kglobal*Y*L^E := by
    rw [source_signed_coefficients_square434]
    exact hFirst
  have hSecondSigned : (∑ n ∈ T, ‖sourceSignedCoefficients434 P eps2 b n‖^2)
      ≤ Kglobal*Y*L^E := by
    rw [source_signed_coefficients_square434]
    exact hSecond
  have hSave := source_finite_comparison_saving434 J c shift S T
    (sourceSignedCoefficients434 P eps1 a) (sourceSignedCoefficients434 P eps2 b)
    Q Hprime Carc Cexp Karc Kglobal Kminor Y L D E
    hL hCexp hKarc hKglobal hKminor hY hMass hQ hr hrhalf
    hFirstSigned hSecondSigned (hArc eps1) hMinor
  rw [norm_mul,source_shared_pattern_sign_norm434,one_mul]
  exact hSave
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductLogCellComparison -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 9000000

/-- Complete width-one logcell product-atom comparisons in all four independent sign channels.
The actual multiplier saving, probability mass, denominator count and radius
are proved here; only the two endpoint energies remain analytic inputs. -/
theorem eventually_source_logcell_four_channel_comparison434
    (cexp dexp Aarc Bsave Carc C1 C2 Chigh C0 vmin Ck D E Karc Kglobal : ℝ) (m0 : ℕ)
    (hc : 0 < cexp) (hd : 0 ≤ dexp) (hdA : dexp < Aarc)
    (hB : 0 ≤ Bsave) (hCarc : Aarc+Bsave ≤ Carc)
    (hChigh : 0 ≤ Chigh) (hv : 0 < vmin) (hC0 : 0 ≤ C0)
    (hCk : 0 ≤ Ck) (hKarc : 0 ≤ Karc) (hKglobal : 0 ≤ Kglobal)
    (hChoice : 2*(C0*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vmin⁻¹)^m0)+D+E) ≤ Bsave) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ {γ₁ γ₂ : Type} [DecidableEq γ₁] [DecidableEq γ₂]
        (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
        (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
        (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
        (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ),
        (∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p) →
        (∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p) →
        (∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h)) →
        (∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h)) →
        (∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ)) →
        (∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ)) →
        (∀ g ∈ G₁, k₁ g ≤ m0) → (∀ g ∈ G₂, k₂ g ≤ m0) →
        (∀ g ∈ G₁, vmin ≤ V₁ g) → (∀ g ∈ G₂, vmin ≤ V₂ g) →
        (G₁.card:ℝ) ≤ C0*Real.log L → (G₂.card:ℝ) ≤ C0*Real.log L →
        ∀ (M N : ℕ), 0 < M → 0 < N →
        ∀ (U1 U2 : ℝ),
        Real.exp (L^cexp-C1) ≤ U1 → Real.exp (L^cexp-C2) ≤ U2 →
        U1 ≤ (M:ℝ) → U2 ≤ (N:ℝ) →
        U1*U2 ≤ Real.exp (Chigh*Real.log L*L^dexp) →
        ∀ (b₁ b₂ : ℕ → ℂ),
        (∀ n ∈ Finset.Ico M (M+3*M), ‖b₁ n‖ ≤ 1) →
        (∀ n ∈ Finset.Ico N (N+3*N), ‖b₂ n‖ ≤ 1) →
        ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
        ∀ (S T : Finset ℤ) (a b : ℤ → ℂ) (Ptw : Finset ℕ) (Y : ℝ), 0 ≤ Y →
        (∑ n ∈ S, ‖a n‖^2) ≤ Kglobal*Y*L^E →
        (∑ n ∈ T, ‖b n‖^2) ≤ Kglobal*Y*L^E →
        (∀ (eps : Bool) (den h : ℕ), 0 < den →
          den ≤ k.natAbs*Nat.ceil (L^Bsave) → h < den →
          (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/(U1*U2)},
            ‖sourceCircleFourierPoly S (sourceSignedCoefficients434 Ptw eps a)
              (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤
            Karc*Y*L^(-(2*(Ck+Bsave+1)+2*D+E))) →
        ∀ (eps1 eps2 : Bool) (sharedSlots : ℕ),
        ‖((if eps1 then (-1:ℂ)^sharedSlots else 1)*
            (if eps2 then (-1:ℂ)^sharedSlots else 1)) *
          (∑ ij ∈ (Finset.range (3*M)).product (Finset.range (3*N)),
            sourceProductShiftCoefficient434 M N
              (sourceProductAtomMass G₁ S₁ k₁ V₁)
              (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ ij *
            (∑ m ∈ S, ∑ n ∈ T,
              if n = m+sourceProductShift434 M N k ij then
                star (sourceSignedCoefficients434 Ptw eps1 a m)*
                  sourceSignedCoefficients434 Ptw eps2 b n else 0))‖ ≤
          (Real.sqrt (2*Karc*Kglobal)+64*Kglobal)*Y*L^(-D) := by
  have hChoice' : 2*(C0*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vmin⁻¹)^m0)+(D+E)) ≤ Bsave := by linarith
  have hMinor := eventually_source_product_logcell_minor_circle434
    cexp dexp Aarc Bsave Carc C1 C2 Chigh C0 vmin (D+E) m0
    hc hd hdA hB hCarc hChigh hv hC0 hChoice'
  have hRadius := eventually_source_product_arc_radius434 cexp Carc C1 C2 hc
  filter_upwards [hMinor,hRadius] with L hMinorL hRadiusL
  refine ⟨hMinorL.1,?_⟩
  intro γ₁ γ₂ _ _ G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N hM hN U1 U2 hMscale hNscale hU1M hU2N hHigh
    b₁ b₂ hb₁ hb₂ k hk hKshift S T a b Ptw Y hY hFirst hSecond hArc
  have hMass := source_original_product_coefficient_mass434
    G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact
    (fun g hg => hv.trans_le (hV₁ g hg)) (fun g hg => hv.trans_le (hV₂ g hg))
    M N (3*M) (3*N) b₁ b₂ hb₁ hb₂
  have hQcap := source_product_rational_denominator_cap434 L Ck Bsave k
    hRadiusL.1 hB hKshift
  have hRad := hRadiusL.2 U1 U2 hMscale hNscale
  have hActualMinor := hMinorL.2 G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N hM hN U1 U2 hMscale hNscale hU1M hU2N hHigh b₁ b₂ hb₁ hb₂ k hk
  refine source_four_channel_comparison_saving434
    ((Finset.range (3*M)).product (Finset.range (3*N)))
    (sourceProductShiftCoefficient434 M N
      (sourceProductAtomMass G₁ S₁ k₁ V₁) (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂)
    (sourceProductShift434 M N k) S T a b (k.natAbs*Nat.ceil (L^Bsave)) Ptw
    (U1*U2) Carc (Ck+Bsave+1) Karc Kglobal 64 Y L D E
    hMinorL.1 (by linarith) hKarc hKglobal (by norm_num) hY
    hMass hQcap hRad.1 hRad.2 hFirst hSecond hArc ?_
  intro theta hOutside
  simpa only [sourceProductMultiplier434,neg_add,sub_eq_add_neg] using hActualMinor theta hOutside
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedCoreInvariant -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 5000000

/-- The literal outside-P part is unchanged by a product of group primes.
No distinctness between these primes and w is required. -/
theorem source_outside_part_shared_invariant434 (P R : Finset ℕ) (w : ℕ)
    (hR : ∀ p ∈ R, p.Prime) (hRP : R ⊆ P) (hw : w ≠ 0) :
    sourceOutsidePart P ((∏ p ∈ R, p)*w) = sourceOutsidePart P w := by
  classical
  let d : ℕ := ∏ p ∈ R, p
  have hd : d ≠ 0 := ne_of_gt (Finset.prod_pos (fun p hp => (hR p hp).pos))
  have hdw : d*w ≠ 0 := mul_ne_zero hd hw
  have hNo (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) : ¬p ∣ d := by
    rw [source_prime_dvd_shared_product434 R hR p hp]
    exact fun hpR => hpP (hRP hpR)
  have hSupport : (d*w).primeFactors.filter (fun p => p ∉ P) =
      w.primeFactors.filter (fun p => p ∉ P) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp,hpd,hpw⟩,hpP⟩
      exact ⟨⟨hp,(hp.dvd_mul.mp hpd).resolve_left (hNo p hp hpP),hw⟩,hpP⟩
    · rintro ⟨⟨hp,hpw,hn⟩,hpP⟩
      exact ⟨⟨hp,dvd_mul_of_dvd_right hpw d,hdw⟩,hpP⟩
  change (∏ p ∈ (d*w).primeFactors with p ∉ P, p^((d*w).factorization p)) = _
  rw [hSupport]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have hpP := (Finset.mem_filter.mp hp).2
  rw [Nat.factorization_mul hd hw,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (hNo p hpPrime hpP),zero_add]

/-- The original prime-slot core, with every alpha/character/prime/residual
factor unchanged, is invariant under this shared dilation. -/
theorem source_literal_core_shared_invariant434
    (P R primeSlot : Finset ℕ) (w q : ℕ) (alpha c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (hR : ∀ p ∈ R, p.Prime) (hRP : R ⊆ P) (hw : w ≠ 0) :
    sourceCore (sourceOutsidePart P ((∏ p ∈ R, p)*w))
      primeSlot alpha c q chi sigma0 sigma1 =
    sourceCore (sourceOutsidePart P w) primeSlot alpha c q chi sigma0 sigma1 := by
  rw [source_outside_part_shared_invariant434 P R w hR hRP hw]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedPhysicalPhase -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 6000000

/-- The original signed source shift survives removal of the shared
product. Positivity of the second endpoint is NOT replaced by toNat. -/
theorem source_shared_signed_shift434 (r d w wp : ℕ) (k : ℤ) (hr : 0 < r) :
    ((r*wp:ℕ):ℤ) = ((r*w:ℕ):ℤ)+k*((r*d:ℕ):ℤ) ↔
      (wp:ℤ)=(w:ℤ)+k*(d:ℤ) := by
  have hr0 : (r:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  push_cast
  constructor
  · intro h
    apply mul_left_cancel₀ hr0
    calc
      (r:ℤ)*(wp:ℤ) = (r:ℤ)*(w:ℤ)+k*((r:ℤ)*(d:ℤ)) := h
      _ = (r:ℤ)*((w:ℤ)+k*(d:ℤ)) := by ring
  · intro h
    rw [h]
    ring

/-- Exact phase cancellation, with independent a1 and a2. -/
theorem source_shared_phase_cancellation434 (r d w wp : ℕ) (a1 a2 : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hw : 0 < w) (hwp : 0 < wp) :
    sourcePhase (r*d) (-(a1+a2))*sourcePhase (r*w) a1*sourcePhase (r*wp) a2 =
      sourcePhase d (-(a1+a2))*sourcePhase w a1*sourcePhase wp a2 := by
  rw [sourcePhase_mul r d hr hd,sourcePhase_mul r w hr hw,sourcePhase_mul r wp hr hwp]
  unfold sourcePhase
  simp only [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Literal harmonic weight and cutoff after n=r*w, D=r*d. The factor
1/r remains exactly once and the original cutoff is evaluated at w/(Z*d). -/
theorem source_shared_harmonic_scalar434 (r d w wp : ℕ) (Z a1 a2 : ℝ)
    (psi : ℝ → ℂ) (hr : 0 < r) (hd : 0 < d) (hw : 0 < w) (hwp : 0 < wp)
    (hZ : 0 < Z) :
    psi (((r*w:ℕ):ℝ)/(Z*((r*d:ℕ):ℝ)))*((r*w:ℕ):ℂ)⁻¹*
      sourcePhase (r*d) (-(a1+a2))*sourcePhase (r*w) a1*sourcePhase (r*wp) a2 =
    (r:ℂ)⁻¹*psi ((w:ℝ)/(Z*(d:ℝ)))*(w:ℂ)⁻¹*
      sourcePhase d (-(a1+a2))*sourcePhase w a1*sourcePhase wp a2 := by
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hRatio : (((r*w:ℕ):ℝ)/(Z*((r*d:ℕ):ℝ))) = (w:ℝ)/(Z*(d:ℝ)) := by
    push_cast
    field_simp
    <;> ring
  rw [hRatio]
  calc
    _ = (psi ((w:ℝ)/(Z*(d:ℝ)))*((r*w:ℕ):ℂ)⁻¹)*
        (sourcePhase (r*d) (-(a1+a2))*sourcePhase (r*w) a1*sourcePhase (r*wp) a2) := by ring
    _ = _ := by
      rw [source_shared_phase_cancellation434 r d w wp a1 a2 hr hd hw hwp]
      push_cast
      simp only [mul_inv_rev]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCollisionCore -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- A free auxiliary prime in P disappears from the original
outside-P core after the exact collision reindex w=p*y. The
prime-slot sum, character, alpha and residual coefficients are kept. -/
theorem source_auxiliary_original_core_invariant434
    (P primeSlot : Finset ℕ) (p w q : ℕ)
    (alpha c : ℕ → ℂ) (chi : DirichletCharacter ℂ q)
    (s0 s1 : ℝ) (hp : p.Prime) (hpP : p ∈ P) (hw : 0 < w) :
    sourceCore (sourceOutsidePart P (p*w))
      primeSlot alpha c q chi s0 s1 =
    sourceCore (sourceOutsidePart P w)
      primeSlot alpha c q chi s0 s1 := by
  have hh := source_literal_core_shared_invariant434 P {p}
    primeSlot w q alpha c chi s0 s1
    (by intro z hz; have hz' : z=p := Finset.mem_singleton.mp hz
        subst z
        exact hp)
    (Finset.singleton_subset_iff.mpr hpP) (Nat.ne_of_gt hw)
  simpa only [Finset.prod_singleton] using hh

/-- The source harmonic 1/w measure pays precisely one 1/p
when charging a free auxiliary p collision. No asymptotic claim. -/
theorem source_auxiliary_harmonic_reindex434 (p y : ℕ) :
    ((p*y:ℕ):ℂ)⁻¹ = (p:ℂ)⁻¹*(y:ℂ)⁻¹ := by
  push_cast
  rw [mul_inv_rev]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryFiniteDivisorReindex -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- True finite divisor charging for an auxiliary prime p in D_C.
No averaging or asymptotic estimate is hidden in this identity. -/
theorem source_auxiliary_divisible_Icc_image434
    (p N : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 N).filter (fun w => p ∣ w) =
      (Finset.Icc 1 (N/p)).image (fun y => p*y) := by
  classical
  ext w
  simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_image]
  constructor
  · rintro ⟨⟨hwpos,hwmax⟩,hd⟩
    obtain ⟨y,rfl⟩ := hd
    have hy : 1 ≤ y := by
      by_contra h
      have hyz : y=0 := Nat.eq_zero_of_not_pos (by omega)
      subst y
      simp at hwpos
    have hymax : y ≤ N/p := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      simpa only [mul_comm] using hwmax
    exact ⟨y,⟨hy,hymax⟩,rfl⟩
  · rintro ⟨y,⟨hy,hymax⟩,rfl⟩
    have hpY : 0 < p*y := Nat.mul_pos hp (by omega)
    have hmax : p*y ≤ N := by
      have hh := (Nat.le_div_iff_mul_le hp).mp hymax
      simpa only [mul_comm] using hh
    exact ⟨⟨hpY,hmax⟩,⟨y,rfl⟩⟩

/-- Generic exact reindex of the actual NATURAL finite harmonic range.
The factor p in the new position is retained, without a fake
independence assumption between a free draw and the source w. -/
theorem source_auxiliary_finite_divisible_sum434
    (p N : ℕ) (hp : 0 < p) (f : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 N, if p ∣ w then f w else 0) =
      ∑ y ∈ Finset.Icc 1 (N/p), f (p*y) := by
  classical
  have hinj : Set.InjOn (fun y : ℕ => p*y) (↑(Finset.Icc 1 (N/p))) := by
    intro y hy z hz he
    exact (mul_left_cancel₀ (Nat.ne_of_gt hp)) he
  calc
    _ = ∑ w ∈ (Finset.Icc 1 N).filter (fun w => p ∣ w), f w := by
      rw [Finset.sum_filter]
    _ = ∑ w ∈ (Finset.Icc 1 (N/p)).image (fun y => p*y), f w := by
      rw [source_auxiliary_divisible_Icc_image434 p N hp]
    _ = _ := Finset.sum_image hinj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryHarmonicCharge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The actual free-auxiliary collision change w=p*y in source03.
It keeps the signed k, the exact new shift k*D, the positive-endpoint
test before Int.toNat, and gains EXACTLY ONE harmonic 1/p.
The final divisor-moment estimate after this identity is separate. -/
theorem source_auxiliary_harmonic_charge434
    (p D N : ℕ) (k : ℤ) (hp : 0 < p)
    (F : ℕ → ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 N,
      if p ∣ w then
        if 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) then
          F w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat)*(w:ℂ)⁻¹
        else 0
      else 0) =
    (p:ℂ)⁻¹ *
      (∑ y ∈ Finset.Icc 1 (N/p),
        if 0 < (y:ℤ)+k*(D:ℤ) then
          F (p*y) (p*((y:ℤ)+k*(D:ℤ)).toNat)*(y:ℂ)⁻¹
        else 0) := by
  classical
  let f : ℕ → ℂ := fun w =>
    if 0 < (w:ℤ)+k*(p:ℤ)*(D:ℤ) then
      F w (((w:ℤ)+k*(p:ℤ)*(D:ℤ)).toNat)*(w:ℂ)⁻¹
    else 0
  change (∑ w ∈ Finset.Icc 1 N, if p ∣ w then f w else 0) = _
  rw [source_auxiliary_finite_divisible_sum434 p N hp f]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hpZ : (0:ℤ)<p := by exact_mod_cast hp
  have hSign :
      (0 < (((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ))) ↔
        (0 < (y:ℤ)+k*(D:ℤ)) := by
    rw [source_auxiliary_signed_shift_scaling434]
    constructor
    · intro hh
      by_contra hn
      have hNeg : (y:ℤ)+k*(D:ℤ) ≤ 0 := by omega
      have hNonpos : (p:ℤ)*((y:ℤ)+k*(D:ℤ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpZ.le hNeg
      omega
    · intro hypos
      exact mul_pos hpZ hypos
  by_cases hPos : 0 < (y:ℤ)+k*(D:ℤ)
  · have hBig := hSign.mpr hPos
    dsimp only [f]
    rw [if_pos hBig,if_pos hPos,
      source_auxiliary_signed_toNat_scaling434 p y D k hp hPos,
      source_auxiliary_harmonic_reindex434]
    ring
  · have hBig : ¬0 < (((p*y:ℕ):ℤ)+k*(p:ℤ)*(D:ℤ)) :=
      fun hh => hPos (hSign.mp hh)
    dsimp only [f]
    simp only [if_neg hBig,if_neg hPos]
    ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedListAssembly -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 6000000

/-- Existing ordered marks, with their exact finite-set membership exposed. -/
theorem source_ordered_marks_mem434 (P : Finset ℕ) (M n : ℕ) (a : Fin M → ℕ) :
    a ∈ orderedBigMarks P M n ↔
      (∀ i, a i ∈ P ∧ a i ∣ n) ∧ Function.Injective a := by
  classical
  simp only [orderedBigMarks,Finset.mem_filter,Fintype.mem_piFinset,
    smallPrimeSupport,Finset.mem_filter]

noncomputable def sourceSharedPrimeSet434 {M : ℕ}
    (E : Finset (Fin M)) (shared : E → ℕ) : Finset ℕ :=
  Finset.univ.image shared

/-- Literal physical mark lists with the source shared slots retained. -/
noncomputable def sourceSharedCompletions434 (P : Finset ℕ) (M : ℕ)
    (E : Finset (Fin M)) (shared : E → ℕ) (w : ℕ) : Finset (Fin M → ℕ) :=
  (orderedBigMarks P M ((∏ p ∈ sourceSharedPrimeSet434 E shared, p)*w)).filter
    (fun a => ∀ i : E, a i = shared i)

noncomputable def sourceSharedAssemble434 {M t : ℕ} (E : Finset (Fin M))
    (shared : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E})
    (b : Fin t → ℕ) (i : Fin M) : ℕ :=
  if hi : i ∈ E then shared ⟨i,hi⟩ else b (e.symm ⟨i,hi⟩)

/-- Reinsert the actual shared labels into the original arbitrary slots.
The clean condition is only that shared primes do not divide w. -/
theorem source_shared_assemble_mem434 {M t : ℕ} (P : Finset ℕ)
    (E : Finset (Fin M)) (shared : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E})
    (w : ℕ) (hP : ∀ p ∈ P, p.Prime) (hs : ∀ i, shared i ∈ P)
    (hsInj : Function.Injective shared) (hAvoid : ∀ i, ¬shared i ∣ w)
    (b : Fin t → ℕ) (hb : b ∈ orderedBigMarks P t w) :
    sourceSharedAssemble434 E shared e b ∈ sourceSharedCompletions434 P M E shared w := by
  classical
  obtain ⟨hbDiv,hbInj⟩ := (source_ordered_marks_mem434 P t w b).mp hb
  apply Finset.mem_filter.mpr
  constructor
  · apply (source_ordered_marks_mem434 P M _ _).mpr
    constructor
    · intro i
      unfold sourceSharedAssemble434
      split_ifs with hi
      · refine ⟨hs ⟨i,hi⟩,dvd_mul_of_dvd_left ?_ w⟩
        exact Finset.dvd_prod_of_mem id (Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩)
      · exact ⟨(hbDiv _).1,dvd_mul_of_dvd_right (hbDiv _).2 _⟩
    · intro i j hij
      by_cases hi : i ∈ E
      · by_cases hj : j ∈ E
        · simp only [sourceSharedAssemble434,dif_pos hi,dif_pos hj] at hij
          exact congrArg Subtype.val (hsInj hij)
        · simp only [sourceSharedAssemble434,dif_pos hi,dif_neg hj] at hij
          exact (hAvoid ⟨i,hi⟩ (by rw [hij]; exact (hbDiv _).2)).elim
      · by_cases hj : j ∈ E
        · simp only [sourceSharedAssemble434,dif_neg hi,dif_pos hj] at hij
          exact (hAvoid ⟨j,hj⟩ (by rw [←hij]; exact (hbDiv _).2)).elim
        · simp only [sourceSharedAssemble434,dif_neg hi,dif_neg hj] at hij
          have hh := congrArg e (hbInj hij)
          simpa only [Equiv.apply_symm_apply] using congrArg Subtype.val hh
  · intro i
    simp only [sourceSharedAssemble434,dif_pos i.property]

/-- Restricting a physical completion gives actual ordered divisors of w,
not divisors of the shared product times w. -/
theorem source_shared_restrict_mem434 {M t : ℕ} (P : Finset ℕ)
    (E : Finset (Fin M)) (shared : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E})
    (w : ℕ) (hP : ∀ p ∈ P, p.Prime) (hs : ∀ i, shared i ∈ P)
    (a : Fin M → ℕ) (ha : a ∈ sourceSharedCompletions434 P M E shared w) :
    (fun j => a (e j)) ∈ orderedBigMarks P t w := by
  classical
  obtain ⟨haMem,haShared⟩ := Finset.mem_filter.mp ha
  obtain ⟨haDiv,haInj⟩ := (source_ordered_marks_mem434 P M _ a).mp haMem
  apply (source_ordered_marks_mem434 P t w _).mpr
  constructor
  · intro j
    have hnR : a (e j) ∉ sourceSharedPrimeSet434 E shared := by
      intro hmem
      obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hmem
      have hh : a (e j) = a i := heq.symm.trans (haShared i).symm
      have hpos := haInj hh
      exact (e j).property (hpos.symm ▸ i.property)
    have hRP : sourceSharedPrimeSet434 E shared ⊆ P := by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      exact hs i
    exact ⟨(haDiv _).1,(source_unshared_divisor_iff434 P
      (sourceSharedPrimeSet434 E shared) w (a (e j)) hP hRP (haDiv _).1 hnR).mp (haDiv _).2⟩
  · intro i j hij
    exact e.injective (Subtype.ext (haInj hij))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedGlobalSupport -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 6000000

/-- A group's support sees only its own shared primes inside the GLOBAL
shared dilation. Prime labels from other groups do not alter its lists. -/
theorem source_shared_intersection_support434 (P R : Finset ℕ) (w : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) :
    smallPrimeSupport P ((∏ p ∈ R,p)*w) = (P ∩ R) ∪ smallPrimeSupport P w := by
  classical
  ext p
  by_cases hp : p ∈ P
  · simp only [smallPrimeSupport,Finset.mem_filter,hp,true_and,Finset.mem_union,
      Finset.mem_inter,(hP p hp).dvd_mul,source_prime_dvd_shared_product434 R hR p (hP p hp)]
  · simp only [smallPrimeSupport,Finset.mem_filter,hp,false_and,Finset.mem_union,
      Finset.mem_inter,or_self]

theorem source_group_shared_intersection434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) (g : G) :
    P g ∩ (Finset.univ.biUnion R) = R g := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨h,hh,hpR⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hp).2
    have he := hDisj g h p (Finset.mem_inter.mp hp).1 (hRP h hpR)
    exact he.symm ▸ hpR
  · intro hp
    exact Finset.mem_inter.mpr ⟨hRP g hp,Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hp⟩⟩

/-- Exact original group-mark list equality at the global and local shared
positions. This discharges the multi-group dilation condition in the list bijection. -/
theorem source_group_marks_global_shared434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) (g : G) (M w : ℕ) :
    orderedBigMarks (P g) M ((∏ p ∈ Finset.univ.biUnion R,p)*w) =
      orderedBigMarks (P g) M ((∏ p ∈ R g,p)*w) := by
  classical
  have hRR : ∀ p ∈ Finset.univ.biUnion R,p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hP g p (hRP g hpg)
  have he : smallPrimeSupport (P g) ((∏ p ∈ Finset.univ.biUnion R,p)*w) =
      smallPrimeSupport (P g) ((∏ p ∈ R g,p)*w) := by
    rw [source_shared_intersection_support434 (P g) _ w (hP g) hRR,
      source_group_shared_intersection434 P R hRP hDisj g,
      source_shared_prime_support434 (P g) (R g) w (hP g) (hRP g)]
  unfold orderedBigMarks
  rw [he]

/-- The actual omega count at every group under the full shared dilation. -/
theorem source_group_count_global_shared434 {G : Type} [Fintype G] [DecidableEq G]
    (P R : G → Finset ℕ) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hRP : ∀ g, R g ⊆ P g)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g=h) (g : G) (w : ℕ)
    (hAvoid : ∀ p ∈ R g, ¬p ∣ w) :
    smallPrimeCount (P g) ((∏ p ∈ Finset.univ.biUnion R,p)*w) =
      (R g).card+smallPrimeCount (P g) w := by
  classical
  have hRR : ∀ p ∈ Finset.univ.biUnion R,p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hP g p (hRP g hpg)
  unfold smallPrimeCount
  rw [source_shared_intersection_support434 (P g) _ w (hP g) hRR,
    source_group_shared_intersection434 P R hRP hDisj g]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr (fun p hp hpw => hAvoid p hp (Finset.mem_filter.mp hpw).2)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSharedListEquiv -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 6000000

/-- Exact bijection of the actual physical completions with the ordered
unshared marks at w. Arbitrary original slot positions are retained. -/
noncomputable def sourceSharedCompletionEquiv434 {M t : ℕ} (P : Finset ℕ)
    (E : Finset (Fin M)) (shared : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E})
    (w : ℕ) (hP : ∀ p ∈ P, p.Prime) (hs : ∀ i, shared i ∈ P)
    (hsInj : Function.Injective shared) (hAvoid : ∀ i, ¬shared i ∣ w) :
    (↑(sourceSharedCompletions434 P M E shared w)) ≃ (↑(orderedBigMarks P t w)) where
  toFun a := ⟨fun j => a.val (e j),source_shared_restrict_mem434 P E shared e w hP hs a.val a.property⟩
  invFun b := ⟨sourceSharedAssemble434 E shared e b.val,
    source_shared_assemble_mem434 P E shared e w hP hs hsInj hAvoid b.val b.property⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    dsimp only [sourceSharedAssemble434]
    split_ifs with hi
    · exact ((Finset.mem_filter.mp a.property).2 ⟨i,hi⟩).symm
    · simp only [Equiv.apply_symm_apply]
  right_inv b := by
    apply Subtype.ext
    funext j
    dsimp only [sourceSharedAssemble434]
    rw [dif_neg (e j).property]
    change b.val (e.symm (e j))=b.val j
    exact congrArg b.val (e.symm_apply_apply j)

/-- Reindex ANY source coefficient test, including tests on both full
physical lists; this is not merely a cardinality identity. -/
theorem source_shared_completion_sum434 {M t : ℕ} (P : Finset ℕ)
    (E : Finset (Fin M)) (shared : E → ℕ) (e : Fin t ≃ {i : Fin M // i ∉ E})
    (w : ℕ) (hP : ∀ p ∈ P, p.Prime) (hs : ∀ i, shared i ∈ P)
    (hsInj : Function.Injective shared) (hAvoid : ∀ i, ¬shared i ∣ w)
    (F : (Fin M → ℕ) → ℂ) :
    (∑ a ∈ sourceSharedCompletions434 P M E shared w, F a) =
      ∑ b ∈ orderedBigMarks P t w, F (sourceSharedAssemble434 E shared e b) := by
  classical
  let ee := sourceSharedCompletionEquiv434 P E shared e w hP hs hsInj hAvoid
  have hh := Fintype.sum_equiv ee.symm
    (fun b => F (sourceSharedAssemble434 E shared e b.val)) (fun a => F a.val)
    (fun b => rfl)
  calc
    _ = ∑ a : ↑(sourceSharedCompletions434 P M E shared w), F a.val :=
      (Finset.sum_coe_sort _ F).symm
    _ = ∑ b : ↑(orderedBigMarks P t w), F (sourceSharedAssemble434 E shared e b.val) := hh.symm
    _ = _ := Finset.sum_coe_sort _ (fun b => F (sourceSharedAssemble434 E shared e b))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSharedSlots -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 4500000

/-- Precisely the shared slots in the original source row operator. -/
def sourceOriginalSharedSlots434 (J ell : ℕ) (C : Finset (Fin J)) :
    Finset (Fin (J+ell)) := (Finset.univ \ C).image (fun i : Fin J => i.castAdd ell)

theorem source_original_shared_slot_mem434 (J ell : ℕ) (C : Finset (Fin J)) (i : Fin J) :
    i.castAdd ell ∈ sourceOriginalSharedSlots434 J ell C ↔ i ∉ C := by
  classical
  simp only [sourceOriginalSharedSlots434,Finset.mem_image,Finset.mem_sdiff,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,hji⟩
    have he : j=i := Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) hji)
    exact he ▸ hj
  · exact fun hi => ⟨i,hi,rfl⟩

theorem source_original_shared_slot_card434 (J ell : ℕ) (C : Finset (Fin J)) :
    (sourceOriginalSharedSlots434 J ell C).card = J-C.card := by
  classical
  unfold sourceOriginalSharedSlots434
  have hinj : Function.Injective (fun i : Fin J => i.castAdd ell) :=
    fun i j h => Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) h)
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]

theorem source_original_free_slot_card434 (J ell : ℕ) (C : Finset (Fin J)) :
    Fintype.card {i : Fin (J+ell) // i ∉ sourceOriginalSharedSlots434 J ell C} = ell+C.card := by
  classical
  rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,
    source_original_shared_slot_card434]
  have hC : C.card ≤ J := by simpa only [Fintype.card_fin] using C.card_le_univ
  omega

/-- No arbitrary enumeration hypothesis is left at the source application:
the complement has exactly t=ell+|C| original slots. -/
noncomputable def sourceOriginalFreeSlotEquiv434 (J ell : ℕ) (C : Finset (Fin J)) :
    Fin (ell+C.card) ≃ {i : Fin (J+ell) // i ∉ sourceOriginalSharedSlots434 J ell C} :=
  (Fintype.equivFinOfCardEq (source_original_free_slot_card434 J ell C)).symm

/-- Source shared-list equality is exactly equality on the retained slots. -/
theorem source_original_shared_list_condition434 (J ell : ℕ) (C : Finset (Fin J))
    (a b : Fin (J+ell) → ℕ) :
    (∀ i : Fin J, i ∉ C → a (i.castAdd ell)=b (i.castAdd ell)) ↔
      (∀ i ∈ sourceOriginalSharedSlots434 J ell C, a i=b i) := by
  constructor
  · intro h i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact h j (Finset.mem_sdiff.mp hj).2
  · intro h i hi
    exact h _ ((source_original_shared_slot_mem434 J ell C i).mpr hi)

/-- The source ell+|C| endpoint marks after removing its actual shared slots. -/
noncomputable def sourceOriginalSharedCompletionEquiv434
    (P : Finset ℕ) (J ell : ℕ) (C : Finset (Fin J))
    (shared : sourceOriginalSharedSlots434 J ell C → ℕ) (w : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hs : ∀ i, shared i ∈ P)
    (hsInj : Function.Injective shared) (hAvoid : ∀ i, ¬shared i ∣ w) :
    (↑(sourceSharedCompletions434 P (J+ell) (sourceOriginalSharedSlots434 J ell C) shared w)) ≃
      (↑(orderedBigMarks P (ell+C.card) w)) :=
  sourceSharedCompletionEquiv434 P _ shared (sourceOriginalFreeSlotEquiv434 J ell C)
    w hP hs hsInj hAvoid
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalSlots -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- For every original residual pattern, the ACTUAL freed first-J
physical slots in group g are exactly the designated probes selected
from its two disjoint source comparison blocks. -/
noncomputable def sourceOriginalProbeFreedSlots434
    {G : Type} [DecidableEq G]
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    Finset (Fin J) :=
  ((Finset.univ : Finset (Fin m)).filter
    (fun j => (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2)).image
      (fun j => j.castLE hmJ)

/-- The literal source03 pattern keeps the remaining first-J slots
shared; all last ell slots are free. -/
noncomputable def sourceOriginalProbeSharedSlots434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    Finset (Fin (J+ell)) :=
  sourceOriginalSharedSlots434 J ell (sourceOriginalProbeFreedSlots434 J m hmJ ν g)

/-- For each source03 pattern, the exact unshared endpoint mark count
is ell+|C_g|, not m+ell and not a uniform t independent of nu. -/
noncomputable def sourceOriginalProbeFreeMarkCount434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) : ℕ :=
  ell + (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card

/-- The actual canonical bijection from the ell+|C_g| free mark
indices to the complement of original physical shared slots. -/
noncomputable def sourceOriginalProbeFreeMarkEquiv434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) ≃
      {i : Fin (J+ell) // i ∉ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g} :=
  sourceOriginalFreeSlotEquiv434 J ell
    (sourceOriginalProbeFreedSlots434 J m hmJ ν g)

/-- The selected designated probe occupies its literal original
physical first-J slot, hence is NOT retained in the shared part. -/
theorem source_original_probe_freed_membership434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (g : G) (j : Fin m)
    (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2) :
    (j.castLE hmJ).castAdd ell ∉
      sourceOriginalProbeSharedSlots434 J ell m hmJ ν g := by
  rw [sourceOriginalProbeSharedSlots434,
    source_original_shared_slot_mem434]
  simp only [sourceOriginalProbeFreedSlots434,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  intro hn
  exact hn ⟨j,hj,rfl⟩

/-- The unshared natural slot count agrees with its actual complement
in the original (J+ell)-slot marked row, for every group/pattern. -/
theorem source_original_probe_free_mark_count434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    Fintype.card {i : Fin (J+ell) //
      i ∉ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g} =
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g := by
  exact source_original_free_slot_card434 J ell
    (sourceOriginalProbeFreedSlots434 J m hmJ ν g)

/-- No probe in either original block uses any of the last ell slots;
their slot embedding is literally the initial first-J injection. -/
theorem source_original_probe_first_J_slot434
    (J ell m : ℕ) (hmJ : m ≤ J) (j : Fin m) :
    ((j.castLE hmJ).castAdd ell).val < J := by
  exact (j.castLE hmJ).isLt
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalGeometry -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Selected SOURCE03 first-m probes correspond exactly to their
original physical slot positions. The first-J cast is injective. -/
theorem source_original_probe_freed_first_m_iff434
    {G : Type} [DecidableEq G]
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (g : G) (j : Fin m) :
    j.castLE hmJ ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν g ↔
      (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2 := by
  classical
  simp only [sourceOriginalProbeFreedSlots434,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,hk,hkj⟩
    have hv : (k:ℕ)=(j:ℕ) :=
      congrArg (fun z : Fin J => z.val) hkj
    have h : k=j := Fin.ext hv
    simpa only [h] using hk
  · intro h
    exact ⟨j,h,rfl⟩

/-- The true comparison probes in EACH big group number at most m,
regardless of J or how many other groups occur. -/
theorem source_original_probe_freed_card_le_m434
    {G : Type} [DecidableEq G]
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card ≤ m := by
  classical
  unfold sourceOriginalProbeFreedSlots434
  calc
    _ ≤ ((Finset.univ : Finset (Fin m)).filter
           (fun j => (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

/-- The physical source03 row identity holds for EVERY selected
residual pattern: |shared slots|+|free slots|=J+ell, with the
right sign and actual first-J free set C_g. -/
theorem source_original_probe_shared_free_card434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card +
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g =
      J+ell := by
  classical
  let C := sourceOriginalProbeFreedSlots434 J m hmJ ν g
  have hC : C.card ≤ J := by
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hh := source_original_shared_slot_card434 J ell C
  change (sourceOriginalSharedSlots434 J ell C).card +
    (ell + C.card) = J+ell
  rw [hh]
  omega

/-- Every source03 comparison physical endpoint has at most ell+m
unshared marks per group, uniformly in J. -/
theorem source_original_probe_free_mark_cap434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g ≤ ell+m := by
  dsimp [sourceOriginalProbeFreeMarkCount434]
  exact Nat.add_le_add_left
    (source_original_probe_freed_card_le_m434 J m hmJ ν g) ell

/-- If a group is NOT in either big-block probe family, NO first-J
coordinate is freed; its only unshared marks are the last ell. -/
theorem source_original_probe_outside_blocks_empty434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (g : G) (hg : g ∉ blockA ∪ blockB) :
    sourceOriginalProbeFreedSlots434 J m hmJ ν g = ∅ := by
  classical
  obtain ⟨_,hA,_,hB⟩ :=
    (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
  ext i
  simp
  intro hi
  obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
  have hsel : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2 :=
    (Finset.mem_filter.mp hj).2
  have hNA : g ∉ blockA := fun hh => hg (Finset.mem_union.mpr (Or.inl hh))
  have hNB : g ∉ blockB := fun hh => hg (Finset.mem_union.mpr (Or.inr hh))
  rcases hsel with ha | hb
  · exact hNA (Finset.mem_product.mp (hA ha)).1
  · exact hNB (Finset.mem_product.mp (hB hb)).1

theorem source_original_probe_outside_blocks_t_equals_ell434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (g : G) (hg : g ∉ blockA ∪ blockB) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g = ell := by
  simp [sourceOriginalProbeFreeMarkCount434,
    source_original_probe_outside_blocks_empty434 blockA blockB J m hmJ ν hν g hg]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalProducts -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Recover a SPECIFIC selected source03 probe's index inside the
actual, variable-size list of unshared endpoint marks, with no
arbitrary bijection passed as a hypothesis. -/
noncomputable def sourceOriginalProbeFreeIndex434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (g : G) (j : Fin m)
    (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) :=
  (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g).symm
    ⟨(j.castLE hmJ).castAdd ell,
      source_original_probe_freed_membership434 J ell m hmJ ν g j hj⟩

/-- Full source03 physical list obtained by assembling its TRUE
shared-list labels with all unshared endpoint marks. The chosen
shared and unshared slots are exactly those induced by the pattern. -/
noncomputable def sourceOriginalProbeAssembledFull434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (free : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    G → Fin (J+ell) → ℕ :=
  fun g => sourceSharedAssemble434
    (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g)
    (shared g) (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g)
    (free g)

/-- Original physical X_A is the product of the TARGET-end
labels in the FIRST global comparison probe block, in the precise
original first-J slot locations. -/
noncomputable def sourceOriginalProbeOriginalTargetX434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (target : G → Fin (J+ell) → ℕ) : ℕ :=
  ∏ z : ν.1, target z.val.1 ((z.val.2.castLE hmJ).castAdd ell)

/-- Original physical X_B is the product of the SOURCE-end
labels in the SECOND global comparison probe block. -/
noncomputable def sourceOriginalProbeOriginalSourceX434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (source : G → Fin (J+ell) → ℕ) : ℕ :=
  ∏ z : ν.2, source z.val.1 ((z.val.2.castLE hmJ).castAdd ell)

/-- X_A expressed in the actual ell+|C_g| target endpoint marks,
with the true physical free-slot coordinate equivalence. -/
noncomputable def sourceOriginalProbeFreeTargetX434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (target : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    ℕ :=
  ∏ z : ν.1, target z.val.1
    (sourceOriginalProbeFreeIndex434 J ell m hmJ ν z.val.1 z.val.2
      (Or.inl z.property))

/-- X_B expressed in the actual ell+|C_g| source endpoint marks,
with the true source03 free-slot coordinate equivalence. -/
noncomputable def sourceOriginalProbeFreeSourceX434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (source : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    ℕ :=
  ∏ z : ν.2, source z.val.1
    (sourceOriginalProbeFreeIndex434 J ell m hmJ ν z.val.1 z.val.2
      (Or.inr z.property))

/-- Each freed designated probe returns its exact original physical
slot after the shared and unshared lists are reassembled. -/
theorem source_original_probe_assemble_chosen434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (free : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (g : G) (j : Fin m)
    (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2) :
    sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared free
      g ((j.castLE hmJ).castAdd ell) =
    free g (sourceOriginalProbeFreeIndex434 J ell m hmJ ν g j hj) := by
  simp [sourceOriginalProbeAssembledFull434,sourceSharedAssemble434,
    sourceOriginalProbeFreeIndex434,
    source_original_probe_freed_membership434 J ell m hmJ ν g j hj]

/-- Exact SOURCE03 first global comparison kernel endpoint X_A:
nothing from the final ell marks, nothing from the shared slots,
no loss of multiplicities in the labelled product. -/
theorem source_original_probe_target_product_identification434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (free : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeOriginalTargetX434 J ell m hmJ ν
      (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared free) =
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν free := by
  unfold sourceOriginalProbeOriginalTargetX434 sourceOriginalProbeFreeTargetX434
  apply Finset.prod_congr rfl
  intro z hz
  exact source_original_probe_assemble_chosen434 J ell m hmJ ν shared free
    z.val.1 z.val.2 (Or.inl z.property)

/-- Exact SOURCE03 second global comparison kernel endpoint X_B:
all source marked labels remain in their original positions. -/
theorem source_original_probe_source_product_identification434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (free : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeOriginalSourceX434 J ell m hmJ ν
      (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared free) =
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν free := by
  unfold sourceOriginalProbeOriginalSourceX434 sourceOriginalProbeFreeSourceX434
  apply Finset.prod_congr rfl
  intro z hz
  exact source_original_probe_assemble_chosen434 J ell m hmJ ν shared free
    z.val.1 z.val.2 (Or.inr z.property)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalSharedCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Exactly the number of original SOURCE03 shared labels,
counting their PHYSICAL slot MULTIPLICITIES: the number
of first-J shared slots summed over every group, plus
the exact number of selected freed (g,probe) slots, equals
J times the number of groups. No assumption that sampled
prime values are distinct is used. -/
theorem source_original_true_actual_shared_slot_count434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hDisjoint : Disjoint ν.1 ν.2) :
    (∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card)
      + (ν.1.card+ν.2.card) =
      (Fintype.card G)*J := by
  classical
  let S := ν.1 ∪ ν.2
  have hFibre (g : G) :
      (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card =
      ((Finset.univ : Finset (Fin m)).filter
        (fun j => (g,j) ∈ S)).card := by
    dsimp [sourceOriginalProbeFreedSlots434,S]
    rw [Finset.card_image_of_injective]
    · simp only [Finset.mem_union]
    · exact Fin.castLE_injective hmJ
  have hFreed :
      (∑ g : G,
        (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card) =
      S.card := by
    calc
      _ = (∑ g : G, ((Finset.univ : Finset (Fin m)).filter
        (fun j => (g,j) ∈ S)).card) := by
          apply Finset.sum_congr rfl
          intro g hg
          exact hFibre g
      _ = S.card :=
        source_original_finite_freed_slot_fiber_card434 m S
  have hEach (g : G) :
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card +
        (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card = J := by
    have h := source_original_probe_shared_free_card434
      J ell m hmJ ν g
    dsimp [sourceOriginalProbeFreeMarkCount434] at h
    omega
  have hSum :
      (∑ g : G,
         (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card) +
      (∑ g : G,
         (sourceOriginalProbeFreedSlots434 J m hmJ ν g).card) =
      (Fintype.card G)*J := by
    rw [←Finset.sum_add_distrib]
    calc
      _ = ∑ _g : G, J := by
        apply Finset.sum_congr rfl
        intro g hg
        exact hEach g
      _ = (Fintype.card G)*J := by simp
  have hCard : S.card = ν.1.card+ν.2.card := by
    dsimp only [S]
    exact Finset.card_union_of_disjoint hDisjoint
  omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeFreeIndexInjective -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Two different original SOURCE03 chosen first-J probe slots
in a fixed BIG group never map to the same free-slot index.
The statement uses the ACTUAL canonical free-index equivalence,
not an externally assumed injection. -/
theorem source_original_probe_free_index_injective434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (g : G) (j k : Fin m)
    (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2)
    (hk : (g,k) ∈ ν.1 ∨ (g,k) ∈ ν.2)
    (hEq :
      sourceOriginalProbeFreeIndex434 J ell m hmJ ν g j hj =
      sourceOriginalProbeFreeIndex434 J ell m hmJ ν g k hk) :
    j = k := by
  let e := sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ ν g
  have h := congrArg e hEq
  have hEq' :
      (⟨(j.castLE hmJ).castAdd ell,
        source_original_probe_freed_membership434
          J ell m hmJ ν g j hj⟩ :
            {i : Fin (J+ell) //
              i ∉ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g}) =
      ⟨(k.castLE hmJ).castAdd ell,
        source_original_probe_freed_membership434
          J ell m hmJ ν g k hk⟩ := by
    simpa only [e,sourceOriginalProbeFreeIndex434,
      Equiv.apply_symm_apply] using h
  have hSlot := congrArg Subtype.val hEq'
  have hVal := congrArg Fin.val hSlot
  exact Fin.ext (by simpa only [Fin.val_castAdd,Fin.val_castLE] using hVal)

/-- The full original A-block probe-to-physical FREE-SLOT
embedding is injective across all groups and original
marked positions, so selected marginals have no collisions
even if numerical prime values coincide in different slots. -/
noncomputable def sourceOriginalProbeTargetAFreeEmbedding434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) :
    ν.1 ↪ (Σ g : G, Fin
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)) where
  toFun z :=
    ⟨z.val.1,
      sourceOriginalProbeFreeIndex434 J ell m hmJ ν
        z.val.1 z.val.2 (Or.inl z.property)⟩
  inj' := by
    intro a b heq
    rcases a with ⟨⟨ga,ja⟩,ha⟩
    rcases b with ⟨⟨gb,jb⟩,hb⟩
    have hg : ga = gb := (Sigma.mk.inj_iff.mp heq).1
    subst gb
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and] at heq
    have hj := source_original_probe_free_index_injective434
      J ell m hmJ ν ga ja jb (Or.inl ha) (Or.inl hb) heq
    subst jb
    rfl

/-- Original B-block SOURCE physical FREE-SLOT embedding is
also collision-free, with its own ν-dependent chosen slots. -/
noncomputable def sourceOriginalProbeSourceBFreeEmbedding434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) :
    ν.2 ↪ (Σ g : G, Fin
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)) where
  toFun z :=
    ⟨z.val.1,
      sourceOriginalProbeFreeIndex434 J ell m hmJ ν
        z.val.1 z.val.2 (Or.inr z.property)⟩
  inj' := by
    intro a b heq
    rcases a with ⟨⟨ga,ja⟩,ha⟩
    rcases b with ⟨⟨gb,jb⟩,hb⟩
    have hg : ga = gb := (Sigma.mk.inj_iff.mp heq).1
    subst gb
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and] at heq
    have hj := source_original_probe_free_index_injective434
      J ell m hmJ ν ga ja jb (Or.inr ha) (Or.inr hb) heq
    subst jb
    rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTruePhysicalMarginals -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The true original ν-pattern TARGET-end free-mark probability
law, with t_g=ell+|C_g| prime slots per group, projects EXACTLY
onto the originally chosen A-block BIG prime labels in the
SOURCE03 indexed prime tuple. Every selected slot retains its
true 1/(p V_g) mass; ALL remaining physical marks are summed
out unconditionally. F can depend arbitrarily on all selected
prime labels, including their arithmetic product and the
original GLOBAL log-cell mask. No fake independence premise. -/
theorem source_original_probe_true_target_A_marginal434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (F : (∀ z : ν.1, {p : ℕ // p ∈ P z.val.1}) → ℝ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g (p : BP g) => p.val) V
    let e := sourceOriginalProbeTargetAFreeEmbedding434
      J ell m hmJ ν
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        F (fun z : ν.1 => x (e z).1 (e z).2)) =
    (∑ a : (∀ z : ν.1, BP (e z).1),
      (∏ z : ν.1, mu (e z).1 (a z)) * F a) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  have hVEq (g : G) :
      V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      _ = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa [BP,prime] using
          (Finset.sum_coe_sort (P g) (fun p : ℕ => 1/(p:ℝ))).symm
  have hmu :
      ∀ g, ∑ p : BP g, mu g p = 1 :=
    (source_original_joint_harmonic_normalized434 BP prime V
      hVpos hVEq).2
  let e := sourceOriginalProbeTargetAFreeEmbedding434
    J ell m hmJ ν
  have hLaw := source_original_variable_BIG_selected_marginal434
    BP t mu hmu e F
  convert hLaw using 1
  apply Finset.sum_congr
  · ext a
    simp
  · intro a ha
    congr 1
/-- The true original ν-pattern SOURCE-end physical free-mark
law projects EXACTLY onto the chosen B-block BIG prime labels,
with original ν-dependent group lengths and true normalized
harmonic product measure. In particular, the designated
SOURCE product X_B has the SAME exact probability law as the
corresponding independent auxiliary D_B product. -/
theorem source_original_probe_true_source_B_marginal434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (F : (∀ z : ν.2, {p : ℕ // p ∈ P z.val.1}) → ℝ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g (p : BP g) => p.val) V
    let e := sourceOriginalProbeSourceBFreeEmbedding434
      J ell m hmJ ν
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        F (fun z : ν.2 => x (e z).1 (e z).2)) =
    (∑ a : (∀ z : ν.2, BP (e z).1),
      (∏ z : ν.2, mu (e z).1 (a z)) * F a) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  have hVEq (g : G) :
      V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      _ = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa [BP,prime] using
          (Finset.sum_coe_sort (P g) (fun p : ℕ => 1/(p:ℝ))).symm
  have hmu :
      ∀ g, ∑ p : BP g, mu g p = 1 :=
    (source_original_joint_harmonic_normalized434 BP prime V
      hVpos hVEq).2
  let e := sourceOriginalProbeSourceBFreeEmbedding434
    J ell m hmJ ν
  have hLaw := source_original_variable_BIG_selected_marginal434
    BP t mu hmu e F
  convert hLaw using 1
  apply Finset.sum_congr
  · ext a
    simp
  · intro a ha
    congr 1
end Green64Analytic.CorrelationSquare

end

