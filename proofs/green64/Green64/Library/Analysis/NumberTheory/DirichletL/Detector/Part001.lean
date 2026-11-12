module

public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Mathlib.Analysis.MellinInversion

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.LowGramExceptional -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CenteredExceptionalCount IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=>sixthRemainder (Ideal.span {z}))

lemma lowGramRemainders_nonzero (F : Finset O) (R : Id) (hR : R∈lowGramRemainders F) : R≠0 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
  exact sixthRemainder_ne_zero _

theorem lowGramRemainders_card (F : Finset O) (G : Id)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0) :
    (lowGramRemainders F).card≤6^(primeSupport G).card := by
  have hlt (R : lowGramRemainders F) (P : Id) : valuation R.val P<6 := by
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp R.property
    rw [←he]
    exact sixthRemainder_valuation_lt _ _
  let code : lowGramRemainders F→(primeSupport G→Fin 6) := fun R P=>⟨valuation R.val P.val,hlt R P.val⟩
  have hinj : Function.Injective code := by
    intro R T he
    apply Subtype.ext
    apply ideal_eq_of_valuation_eq (lowGramRemainders_nonzero F R.val R.property)
      (lowGramRemainders_nonzero F T.val T.property)
    intro P
    by_cases hp : P∈primeSupport G
    · exact congrArg Fin.val (congrFun he ⟨P,hp⟩)
    · obtain ⟨r,hr,her⟩ := Finset.mem_image.mp R.property
      obtain ⟨t,ht,het⟩ := Finset.mem_image.mp T.property
      rw [←her,←het,sixthRemainder_valuation,sixthRemainder_valuation,hres r hr P hp,hres t ht P hp]
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hh

theorem lowGramExceptional_raw_count (F : Finset O) (G : Id) (H : ℝ) (hH : 0≤H)
    (hF : ∀z∈F,z≠0)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)
    (hN : ∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H) :
    (F.card:ℝ)≤768*(6:ℝ)^(primeSupport G).card*H^(1/6:ℝ) := by
  have hh := element_count_remainder_family F (lowGramRemainders F)
    (lowGramRemainders_nonzero F) H hH hF (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hN
  calc
    _ ≤ ∑R∈lowGramRemainders F,768*(H/(Ideal.absNorm R:ℝ))^(1/6:ℝ) := hh
    _ ≤ ∑_R∈lowGramRemainders F,768*H^(1/6:ℝ) := by
      apply Finset.sum_le_sum
      intro R hR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (div_nonneg hH (Nat.cast_nonneg _)) _ (by norm_num)
      exact div_le_self hH (norm_one_le (lowGramRemainders_nonzero F R hR))
    _ = (lowGramRemainders F).card*(768*H^(1/6:ℝ)) := by simp
    _ ≤ ((6:ℝ)^(primeSupport G).card)*(768*H^(1/6:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGramRemainders_card F G hres
    _ = _ := by ring

theorem lowGramExceptional_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀G : Id,G≠0→∀F : Finset O,∀H : ℝ,0≤H→
      (∀z∈F,z≠0)→
      (∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)→
      (∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H)→
      (F.card:ℝ)≤C*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/3) (by positivity)
  refine ⟨768*C^3,by positivity,?_⟩
  intro G hG F H hH hF hres hN
  have hp : (6:ℝ)^(primeSupport G).card≤C^3*(Ideal.absNorm G:ℝ)^ε := by
    calc
      _ ≤ ((2:ℝ)^3)^(primeSupport G).card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2:ℝ)^(primeSupport G).card)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (C*(Ideal.absNorm G:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) (hb G hG) 3
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm G))]
        congr 2
        norm_num
  apply (lowGramExceptional_raw_count F G H hH hF hres hN).trans
  calc
    _ ≤ 768*(C^3*(Ideal.absNorm G:ℝ)^ε)*H^(1/6:ℝ) := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramFrequencySummation -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=>bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=>hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤R
  · apply DescentFiberCost.finite_element_count_real E R hr
    intro k hk
    simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=>hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

theorem exceptional_frequency_weighted_sum (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0<K ∧ ∀ G : Ideal O, G≠0 → ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      (∀ k∈E,∀ P∉IdealMobiusDivisorSum.primeSupport G,
        CenteredExceptionalCount.valuation (Ideal.span {k}) P % 6=0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤
        K*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := ProbePhysical.lowGramExceptional_count ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro G hG E H hH hE hres
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    (C*(Ideal.absNorm G:ℝ)^ε) (1/6) H (by positivity) (by norm_num) hH (by
      intro F hFE R hR hN
      exact hcount G hG F R hR.le (fun k hk=>hE k (hFE hk))
        (fun k hk=>hres k (hFE hk)) hN)
  convert hh using 1
  ring

end SevenEighths.ProbeGramFrequencySummation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.Phase -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def G (a : O) : ℂ := fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

def reciprocitySign (a b : O) : ℂ :=
  (quadraticRaySign (residue a) (residue b) : ℂ)

theorem G_mul (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring

theorem reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]

theorem reciprocitySign_sq (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb

theorem reciprocitySign_cube_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  have hs := reciprocitySign_sq a b ha hb
  calc
    _ = reciprocitySign a b ^ 2 * reciprocitySign a b := by ring
    _ = reciprocitySign a b := by rw [hs, one_mul]

theorem G_completed_index (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n)) :
    G (c * n ^ 3) = G c * reciprocitySign c n * G (n ^ 3) := by
  have hn3 : EisensteinEPrimaryPhase.odd (residue (n ^ 3)) := by
    rw [show n ^ 3 = (n * n) * n by ring, residue_mul, residue_mul]
    exact QuadraticAllOddCRT.odd_mul _ _ (QuadraticAllOddCRT.odd_mul _ _ hn hn) hn
  rw [G_mul c (n ^ 3) hc hn3, reciprocitySign_cube_right c n hc hn]
  ring

theorem quadraticRayValue_cube (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]

theorem G_cube (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.Completed -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3

def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0

def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))

theorem completedCorrection_eq_phase (I J : Ideal O) :
    completedCorrection I J = rayMask (completedIndex I J) *
      star (ProbePhase.G (completedIndex I J)) := rfl

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)

def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J

def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J

def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2

def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2

def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ

theorem correctionCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ‖correctionCoeff χ‖) ≤ 32 := by
  have h := phaseCoeff_sum_norm_le (fun r => star (fixedGQuotientValue r)) 2
    (fun u => by simpa only [norm_star] using fixedGQuotientValue_norm_le_two (u : RayRing))
  simpa only [correctionCoeff] using h.trans_eq (by norm_num : (16 : ℝ) * 2 = 32)

theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]

theorem completedMask_zero_of_excluded (S : Finset (Ideal O)) (D I J p : Ideal O)
    (hp : p ∈ S) (hpdiv : p ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  unfold completedMask
  rw [ite_eq_right]
  intro h
  exact h.2 p hp hpdiv

theorem completedMask_zero_of_not_marked (S : Finset (Ideal O)) (D I J : Ideal O)
    (hD : ¬D ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  simp [completedMask, hD]

theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)

theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring

theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])

theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])

theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]

theorem correctedCompletedT_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ χ : RayCharacter, ‖markedCompletedT S D (rayMonoid χ * Ψ) W X‖ ≤ B) :
    ‖correctedCompletedT S D Ψ W X‖ ≤ 32 * B := by
  rw [correctedCompletedT_ray_expansion S D Ψ W hW X hX]
  calc
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X‖ := norm_sum_le _ _
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ‖ * B := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound χ) (norm_nonneg _)
    _ = (∑ χ : RayCharacter, ‖correctionCoeff χ‖) * B := (Finset.sum_mul ..).symm
    _ ≤ 32 * B := mul_le_mul_of_nonneg_right correctionCoeff_sum_norm_le hB

end SevenEighths.ProbeCompleted
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhaseCancellation -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)

theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))

theorem completed_phase_cancel (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal (c * n ^ 3))) :
    star (G (c * n ^ 3)) * (G c * reciprocitySign c n * G (n ^ 3)) = 1 := by
  rw [← G_completed_index c n hc hn]
  apply G_conjugate_cancel _ _ hu
  rw [show c * n ^ 3 = c * ((n * n) * n) by ring]
  simp only [residue_mul]
  exact odd_mul _ _ hc (odd_mul _ _ (odd_mul _ _ hn hn) hn)

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PrimePower -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def primeGauss (p : O) (hp : p ≠ 0) (χ : MulChar (O ⧸ Ideal.span {p}) ℂ)
    (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

theorem primePowerGauss_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) χ h hG

theorem primePowerGauss_zero_off_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [← Ideal.span_singleton_pow, map_pow]
  rw [hn, Nat.cast_pow]

theorem primePowerGauss_nonprincipal_extra_divisibility (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [hzero, mul_zero]

theorem primePowerGauss_principal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussValuation -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_at_pow_nonprincipal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero χ n (p ^ j) =
      if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp.ne_zero χ 1
      else 0 := by
  by_cases he : j = n
  · subst j
    rw [ite_eq_left rfl]
    simpa only [mul_one] using primePowerGauss_lift p hp.ne_zero χ n 1
  rw [ite_eq_right he]
  rcases lt_or_gt_of_ne he with hjn | hnj
  · apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · have hle : n ≤ j := Nat.le_of_lt hnj
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [heq]
    apply primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero χ hχ
    exact dvd_pow_self p (by omega)

theorem primePowerGauss_at_pow_principal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp.ne_zero ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero 1 n (p ^ j) =
      (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
      (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp.ne_zero
  have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 := by
    rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})),
      Nat.cast_one]
    rfl
  rcases lt_trichotomy j n with hjn | he | hnj
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self]
    apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · subst j
    have hnot : ¬p ∣ (1 : O) := by simpa only [isUnit_iff_dvd_one] using hp.not_isUnit
    simpa only [mul_one, ite_eq_right hnot, ite_eq_right (Nat.not_succ_le_self n),
      ite_eq_left (le_refl n), zero_sub, mul_neg_one] using
      primePowerGauss_principal p hp.ne_zero hψ n 1
  · have hle : n ≤ j := by omega
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : p ∣ p ^ (j - n) := dvd_pow_self p (by omega)
    rw [heq, primePowerGauss_principal, ite_eq_left hd, ite_eq_left (by omega : n + 1 ≤ j),
      ite_eq_left hle, hcard, pow_succ]
    ring
    exact hψ

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RadialMellin -/

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace SevenEighths.ProbeRadialMellin

def laplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t*r : ℝ))

lemma mellin_real (f : ℝ → ℂ) (s : ℝ) :
    mellin f (s : ℂ) = ∫ r : ℝ in Ioi 0, (r^(s-1) : ℝ) • f r := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open EisensteinSchwartzPoisson

def paperConstant : ℝ := 2*Real.pi/Real.sqrt 3

lemma paperConstant_pos : 0<paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0<t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0<t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

lemma positive_source_mellin (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) : 0<(mellin W (s:ℂ)).re ∧ (mellin W (s:ℂ)).im=0 := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (s:ℂ)
  have hr : ∀r, W r = ((W r).re:ℂ) := by
    intro r
    apply Complex.ext <;> simp [hreal]
  have he : mellin W (s:ℂ) =
      (((∫ r : ℝ in Ioi 0, r^(s-1)*(W r).re):ℝ):ℂ) := by
    rw [mellin_real, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [hr r, Complex.real_smul, Complex.ofReal_mul]
    simp
  rw [he]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  have hi : IntegrableOn (fun r : ℝ => r^(s-1)*(W r).re) (Ioi 0) := by
    have hh := ((mellinConvergent_real W s).mp hc).re
    simpa only [RCLike.smul_re] using! hh
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
  · have hset : Function.support (fun r : ℝ => r^(s-1)*(W r).re) ∩ Ioi 0 =
        Function.support (fun r : ℝ => (W r).re) := by
      ext r
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · intro hh
        exact fun h => hh.1 (by rw [h, mul_zero])
      · intro hh
        have hw : W r≠0 := fun h => hh (by rw [h]; rfl)
        have hp := ha.trans_le (hW hw).1
        exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hp _).ne' hh, hp⟩
    rw [hset]
    apply ((Complex.continuous_re.comp W.continuous).isOpen_support).measure_pos volume
    by_contra h
    apply hne
    ext r
    have hh : (W r).re=0 := by
      by_contra hn
      exact h ⟨r,hn⟩
    change W r = 0
    rw [hr r, hh, Complex.ofReal_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (hnonneg r)

theorem radial_mellin_positive (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    0<(mellin (paperRadialFourier W) (s:ℂ)).re ∧
      (mellin (paperRadialFourier W) (s:ℂ)).im=0 := by
  obtain ⟨hp, hz⟩ := positive_source_mellin W a b ha hW hreal hnonneg hne (1-s)
  have hh : mellin W (1-(s:ℂ)) = ((mellin W ((1-s:ℝ):ℂ)).re:ℂ) := by
    rw [show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ext (by simp) (by simpa using hz)
  rw [radial_mellin_identity W a b ha hW (s:ℂ) hs hs1, hh]
  have hpow : (paperConstant:ℂ)^(1-2*(s:ℂ)) = ((paperConstant^(1-2*s):ℝ):ℂ) := by
    rw [show 1-2*(s:ℂ)=((1-2*s:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow paperConstant_pos.le]
  rw [hpow, show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_im, and_true]
  exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos paperConstant_pos _)
    (Real.Gamma_pos_of_pos hs)) (Real.Gamma_pos_of_pos (by linarith))) hp

theorem radial_mellin_one_sixth_pos (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    0<(mellin (paperRadialFourier W) (1/6)).re ∧
      (mellin (paperRadialFourier W) (1/6)).im=0 := by
  simpa using radial_mellin_positive W a b ha hW hreal hnonneg hne (1/6)
    (by norm_num) (by norm_num)

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0<z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicReflectionKernel.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0<w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0<lo) :
    ∃ (n : ℕ) (C : ℝ), 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

theorem radial_mellin_analytic (W : SchwartzMap ℝ ℂ) :
    AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} :=
  (radial_mellin_differentiable W).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem radial_mellin_strip_rapid (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C/(1+|t|)^N := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW lo hi hlo N
  refine ⟨C,hC,fun σ hσ t => (le_div_iff₀ (by positivity)).mpr ?_⟩
  simpa only [mul_comm] using hb σ hσ t

theorem radial_mellin_vertical_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0<σ) :
    Complex.VerticalIntegrable (mellin (paperRadialFourier W)) σ := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ => mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (radial_mellin_analytic W _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using CubicReflectionKernel.weighted_two_to_cauchy
      (norm_nonneg _) t (hb σ ⟨le_rfl,le_rfl⟩ t)

theorem radial_mellin_inverse_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*
      mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
  have hi := radial_mellin_vertical_integrable W a b ha hW σ hσ
  apply (hi.norm.const_mul (x^(-σ))).mono'
  · have hm := hi.aestronglyMeasurable
    have hc : Continuous (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((σ:ℂ)+t*Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable.mul hm
  · exact Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem radial_mellin_inversion (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    mellinInv σ (mellin (paperRadialFourier W)) x = paperRadialFourier W x :=
  mellinInv_mellin_eq σ (paperRadialFourier W) hx
    (radial_mellin_convergent W σ hσ)
    (radial_mellin_vertical_integrable W a b ha hW σ hσ)
    (radial_continuous W).continuousAt

theorem radial_mellin_one_sixth_ne_zero (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    mellin (paperRadialFourier W) (1/6) ≠ 0 := by
  intro h
  have hp := (radial_mellin_one_sixth_pos W a b ha hW hreal hnonneg hne).1
  rw [h] at hp
  exact (lt_irrefl 0) hp

end SevenEighths.ProbeRadialMellin

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg := by
  exact Complex.ofRealCLM.contDiff.neg.cexp

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ)^n*expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1+x)^n*‖iteratedFDeriv ℝ i expNeg x‖ ≤ (n.factorial : ℝ)*Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+x) (by linarith : 0 ≤ 1+x) n)
  calc
    _ ≤ (Real.exp (1+x)*(n.factorial : ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1+x)+(-x) = 1 by ring]
      ring

def productProfile (Ω V T : ℝ → ℂ) (A B C s : ℝ) : ℂ :=
  Ω s*(1-V (A*s))*expNeg (B*s)*T (C*s)

def inverseProfile (W V : ℝ → ℂ) (R x : ℝ) : ℂ := W x*V (R*x)

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (A B C : ℝ) :
    HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap (logSource_smooth Ω V T hΩ hV hT A B C)

@[simp] lemma logSource_apply (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C y : ℝ) :
    logSource Ω V T hΩc hΩ hV hT A B C y =
      Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y) := rfl

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesBounds -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  obtain ⟨CΩ,hCΩ,hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorFourier -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C/R^N := by
  obtain ⟨C,hC,hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J+N)
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
    (hb A B D hA hB hD)

theorem logSource_product_inversion (Ω V T : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B D x y : ℝ) :
    logSourceFun Ω V T A B D (x+y) =
      ∫ t : ℝ, FourierBridge.logPhase t x * FourierBridge.logPhase t y *
        (𝓕 (logSource Ω V T hΩc hΩ hV hT A B D)) t := by
  have hh := FourierBridge.schwartz_log_inversion
    (logSource Ω V T hΩc hΩ hV hT A B D) (x+y)
  change logSourceFun Ω V T A B D (x+y) = _ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← FourierBridge.logPhase_add]
  congr 1
  simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
  congr 2
  ring_nf

end
end SevenEighths.HeckeDetectorFourier

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*FourierBridge.logPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (FourierBridge.logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*FourierBridge.logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, FourierBridge.logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
  rw [FourierBridge.schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
    rw [← FourierBridge.logPhase_add]
    simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end SevenEighths.HeckeDetectorFourier

end OAI

end

