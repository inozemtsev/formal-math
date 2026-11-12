module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reflection / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reflection.Brackets -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance bracketField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance bracketFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem marked_bracket_cube (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (n b : Eis) :
    bracket (actualSextic P hg) 0 (Ideal.Quotient.mk P (n*b^3)) =
      (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ *
      (idealRowHom n P)⁻¹^2 * (if IsCoprime P (Ideal.span {b}) then 1 else 0) := by
  have h6 : (actualSextic P hg (Ideal.Quotient.mk P b))^6 =
      if b ∈ P then 0 else 1 := by
    simpa only [map_pow] using canonicalSextic_sixth_power_mask P hg b
  have h6' : (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 0 ∨
      (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 1 := by
    rw [h6]; split_ifs <;> simp
  let ψ : Eis →* ℂ := (actualSextic P hg).toMonoidHom.comp (Ideal.Quotient.mk P).toMonoidHom
  have he := InverseMoment.inverse_square_cube_mask ψ n b h6'
  change ((actualSextic P hg) (Ideal.Quotient.mk P (n*b^3)))⁻¹^2 =
    ((actualSextic P hg) (Ideal.Quotient.mk P n))⁻¹^2 *
      ((actualSextic P hg) (Ideal.Quotient.mk P b))^6 at he
  simp only [bracket,show (0:ℕ) ≠ 4 by decide,↓reduceIte,
    MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),inv_pow]
  simp only [inv_pow] at he
  rw [he,rootCard_eq_sqrt_absNorm,idealRowHom_prime n P hg,h6,
    SixthPowerAverage.prime_coprime_span_iff]
  by_cases hb : b ∈ P <;> simp [hb]

theorem marked_bracket_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Eis) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0 (Ideal.Quotient.mk (P i) (n*b^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (idealRowHom n (∏ i, P i))⁻¹^2 *
      (if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0) := by
  simp_rw [marked_bracket_cube]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  have hn : (∏ i, (Real.sqrt (Ideal.absNorm (P i) : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ := by
    rw [map_prod,Nat.cast_prod,Real.sqrt_prod,Complex.ofReal_prod,Finset.prod_inv_distrib]
    intro i hi
    positivity
  have hc : (∏ i, (idealRowHom n (P i))⁻¹^2) = (idealRowHom n (∏ i, P i))⁻¹^2 := by
    rw [map_prod,Finset.prod_pow,Finset.prod_inv_distrib]
  have hm : (∏ i, if IsCoprime (P i) (Ideal.span {b}) then (1:ℂ) else 0) =
      if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0 := by
    classical
    by_cases h : ∀ i, IsCoprime (P i) (Ideal.span {b})
    · simp [h,IsCoprime.prod_left (fun i _ => h i)]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hp : ¬ IsCoprime (∏ i, P i) (Ideal.span {b}) := by
        intro hp
        exact hi (hp.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem P (Finset.mem_univ i)))
      rw [ite_eq_right hp]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [hn,hc,hm]

theorem marked_bracket_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  rw [marked_bracket_product,InverseMoment.inverseCubicKernel_eq_inverse_square,
    (primaryGenerator_spec b hb).1]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Branch -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance branchFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem residual_branch_zero (K : Ideal Eis) (hK : Admissible K) (n b : Ideal Eis) :
    reflectedBranch (fun P : PrimeIndex K => P.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      quadraticRow K (primaryGenerator (n*b)) := by
  simp only [reflectedBranch,reflectedLocalPiece,show (1:ℕ) ≠ 4 by decide,↓reduceIte]
  have hh := residual_bracket_product (fun P : PrimeIndex K => P.val)
    (admissiblePrimeGood K hK) 1 (primaryGenerator n) (primaryGenerator b)
  simp only [one_mul] at hh
  rw [hh,← quadraticRow_eq_primeIndex K hK,← quadraticRow_eq_primeIndex K hK,
    canonical_quadraticRow_one K hK,one_mul,primaryGenerator_mul]

theorem marked_branch_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  simpa only [reflectedBranch,reflectedLocalPiece,show (0:ℕ) ≠ 4 by decide,↓reduceIte]
    using marked_bracket_hybrid P hg n b hb

theorem moving_branches_hybrid {ι : Type*} [Fintype ι]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [residual_branch_zero K hK n b,marked_branch_zero P hg n b hb]
  ring

theorem frozen_moving_branches_hybrid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (F : κ → Ideal Eis) [∀ i, (F i).IsMaximal] (hf : ∀ i, λ₀ ∉ F i)
    (j : κ → ℕ) (e : κ → Fin 3) (β : Ideal Eis → Ideal Eis → ℂ)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b) *
      (reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
        (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
        (if IsCoprime K (∏ i, P i) then 1 else 0)) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b)) *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [moving_branches_hybrid K hK P hg n b hb]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Frozen -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by rw [← mul_pow,mul_inv_cancel₀ ha,one_pow,one_mul]

theorem general_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  if j=4 then tau χ ((quotientTrace p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((quotientTrace p hp).mulShift (-1)) j*tau χ (quotientTrace p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((actualSextic P hg)⁻¹)^2 else (actualSextic P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    rw [exceptional_local_phase _ _ _ _ _ _ hs]
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      rw [marked_local_phase _ _ _ _ _ _ he]
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Cross -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B U : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = U) :
    (∏ i ∈ U, ((∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : U.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : U.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_assoc]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.IdealBridge -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance idealBridgeFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem admissible_primeIndex_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P : PrimeIndex K, P.val) = K := by
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hK.1).mp hK.2.1
  have hv : (CompletedGauss.primeSupport K).val = UniqueFactorizationMonoid.normalizedFactors K := by
    simpa only [CompletedGauss.primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport K, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport K).val.prod := (Finset.prod_val _).symm
    _ = K := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hK.1

theorem idealRowHom_cube_eq_quadratic (K : Ideal Eis) (hK : Admissible K) (z : Eis) :
    idealRowHom z K ^ 3 = quadraticRow K z := by
  conv_lhs => rw [← admissible_primeIndex_product K hK,map_prod,← Finset.prod_pow]
  rw [quadraticRow_eq_primeIndex K hK]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ) ≠ 0)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime z P.val (admissiblePrimeGood K hK P)]

theorem residual_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R : Finset ι) (hR : Admissible (∏ i ∈ R, P i))
    (n b : Ideal Eis) :
    (∏ i ∈ R, bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) =
      idealRowHom (primaryGenerator (n*b)) (P i)^3 := by
    have he := residual_bracket_cube (P i) (hg i) 1 (primaryGenerator n) (primaryGenerator b)
    simpa only [one_mul,map_one,one_pow,primaryGenerator_mul,idealRowHom_prime _ (P i) (hg i)] using he
  simp_rw [hl]
  rw [Finset.prod_pow,← map_prod,idealRowHom_cube_eq_quadratic _ hR]

theorem marked_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (S : Finset ι) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  have he := marked_bracket_hybrid (fun i : S => P i.val) (fun i => hg i.val) n b hb
  have hl : (∏ i : S, bracket (actualSextic (P i.val) (hg i.val)) 0
      (Ideal.Quotient.mk (P i.val) (primaryGenerator n*(primaryGenerator b)^3))) =
      ∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) := by
    exact Finset.prod_coe_sort S (fun i => bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)))
  rw [hl] at he
  simpa only [Finset.prod_coe_sort] using he

theorem full_branch_sum_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hSj : ∀ i ∈ S, j i = 0)
    (hR : Admissible (∏ i ∈ R, P i)) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∑ e : ι → Fin 3, reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)) =
      (∏ i ∈ F, bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  trans ∏ i, bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  · exact (prod_bracket_eq_full_branches P hg j (primaryGenerator n) (primaryGenerator b)).symm
  let v := fun i => bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  have hr : (∏ i ∈ R, v i) = quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
    rw [← residual_bracket_finset P hg R hR n b]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hRj i hi]
  have hs : (∏ i ∈ S, v i) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
    rw [← marked_bracket_finset P hg S n b hb]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hSj i hi]
  have hv : (∏ i, v i) = (∏ i ∈ R, v i)*(∏ i ∈ S, v i)*(∏ i ∈ F, v i) := by
    rw [← Finset.prod_union hRS,← Finset.prod_union hF,hu]
  change (∏ i, v i) = _
  rw [hv,hr,hs]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance threeBlockFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def residualWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (R F : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, MixedCrossSeparation.crossSymbol p hg i k^4)*
    (residualPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^4)

def markedWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (P F : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, MixedCrossSeparation.crossSymbol p hg i k^2)*
    (markedPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^2)

def frozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

theorem activePhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0) :
    D.activePhase hp hg j = residualWithFrozen hp hg c R F *
      markedWithFrozen hp hg c P F * frozenPhase D hp hg j F := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c (hp i) (hg i)
    else markedPrimeScalar (p i) c (hp i) (hg i)
  let v : ι → ℂ := fun i => (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)
  have hm : (∏ i ∈ R ∪ P, v i) = ∏ i ∈ R ∪ P,
      (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [v,hRj i hr,l,hr,ite_true]
      rw [controlled_residual_phase]
      ring
    · have hp' : i ∈ P := (Finset.mem_union.mp hi).resolve_left hr
      simp only [v,hPj i hp',l,hr,ite_false]
      rw [controlled_marked_phase]
      ring
  have hfull : D.activePhase hp hg j = (∏ i ∈ R ∪ P, v i)*frozenPhase D hp hg j F := by
    change (∏ i, v i) = (∏ i ∈ R ∪ P, v i)*(∏ i ∈ F, v i)
    rw [← Finset.prod_union hF,hu]
  rw [hfull,hm,ordered_cross_frozen_partition _ l 4 2 R P F hRP hF hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hRP,mul_one]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [l,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FrozenSplit -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance frozenSplitFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenArgument [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ F, frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i)

def frozenCore [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, frozenPrimeScalar (p i) c (hp i) (hg i) (j i) *
    frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k)

theorem frozen_cofactor_split (hp : ∀ i, p i ≠ 0) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (i : ι) (hi : i ∈ F) :
    cofactor p i = (∏ k ∈ F.erase i, p k)*(∏ k ∈ R, p k)*(∏ k ∈ S, p k) := by
  apply mul_left_cancel₀ (hp i)
  rw [prime_mul_cofactor,← hu,Finset.prod_union hF,Finset.prod_union hRS,
    ← Finset.mul_prod_erase F p hi]
  ring

theorem frozenPhase_split [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (R S F : Finset ι) (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F)
    (hu : (R ∪ S) ∪ F = Finset.univ) :
    frozenPhase D hp hg j F = frozenCore hp hg c j F *
      frozenArgument hg j F (∏ i ∈ R, p i) * frozenArgument hg j F (∏ i ∈ S, p i) := by
  unfold frozenPhase
  simp_rw [controlled_frozen_phase]
  have he (i : ι) (hi : i ∈ F) :
      frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (cofactor p i) =
      (frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k))*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ R, p k)*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ S, p k) := by
    rw [frozen_cofactor_split hp R S F hRS hF hu i hi,map_mul,map_mul]
    ring
  rw [Finset.prod_congr rfl he]
  simp only [Finset.prod_mul_distrib,frozenCore,frozenArgument,MonoidHom.finsetProd_apply]

omit [Fintype ι] in
theorem frozenArgument_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) (z : Eis) :
    ‖frozenArgument hg j F z‖ ≤ 1 := by
  simp only [frozenArgument,MonoidHom.finsetProd_apply,norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    unfold frozenCofactorCharacter
    split_ifs
    · exact FiniteRayExpansion.norm_char_le_one (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)
    · exact FiniteRayExpansion.norm_char_le_one ((actualSextic (Ideal.span {p i}) (hg i))^(2*j i+2))
        (Ideal.Quotient.mk (Ideal.span {p i}) z)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Ramified -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance ramifiedFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def ramifiedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∏ i ∈ S, unitArgumentFactor (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (u.val*λ₀^m))

theorem ramifiedPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
    rfl
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Norms -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance phaseNormField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseNormFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem crossSymbol_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖MixedCrossSeparation.crossSymbol p hg i k‖ = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol,map_pow,ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm h6

theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)

theorem markedPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 0 (by decide)
  rw [controlled_marked_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^2‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 1 (by decide)
  rw [controlled_residual_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^4‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,residualPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hR : (∏ k ∈ R.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hR,hF,one_mul]

theorem markedWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,markedPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hP : (∏ k ∈ P.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hP,hF,one_mul]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Coefficient -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance coefficientFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def sourceRowPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (R F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ R, p i)

def sourceSlotPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  markedWithFrozen hp hg c S F * ramifiedBlock hg (fun _ => 0) S
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ S, p i)

def sourceFrozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  star D.fixedFactor * frozenCore hp hg c j F * ramifiedBlock hg j F
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

def sourceColumn [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b *
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

theorem mixed_coefficient_hybrid [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg (markedActiveExponent S j) R F u m * sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m *
      sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m) *
      sourceColumn D s hc hg (markedActiveExponent S j) F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hrj : ∀ i ∈ R, markedActiveExponent S j i = 1 := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hRS hi hs
    simp only [markedActiveExponent,hn,ite_false,hRj i hi]
  have hsj : ∀ i ∈ S, markedActiveExponent S j i = 0 := by
    intro i hi
    simp only [markedActiveExponent,hi,ite_true]
  have hmask : IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro k hk
    exact hcop (fun h => Finset.disjoint_left.mp hRS hi (h ▸ hk))
  rw [mixed_model_coefficient,modelRowPhase_three_blocks D s hp hg hcop hprimary R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj,
    frozenPhase_split D hp hg (markedActiveExponent S j) R S F hRS hF hu,← Finset.mul_sum,
    full_branch_sum_hybrid (fun i => Ideal.span {p i}) hg R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj hR n b hb,ite_eq_left hmask,mul_one]
  unfold sourceRowPhase sourceSlotPhase sourceFrozenPhase sourceColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Independent -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance independentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem ramifiedBlock_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖ramifiedBlock hg j S u m‖ = 1 := by
  unfold ramifiedBlock
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact unitArgumentFactor_norm _ _ _ (unit_ramified_quotient_ne_zero _ (hg i) u m)

theorem sourceRowPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (R F : Finset ι) (hd : Disjoint R F) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s hp hg j R F u m‖ ≤ 1 := by
  rw [sourceRowPhase,norm_mul,norm_mul,residualWithFrozen_norm D hp hg hchar hcop R F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

theorem sourceSlotPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    ‖sourceSlotPhase s hp hg j S F u m‖ ≤ 1 := by
  rw [sourceSlotPhase,norm_mul,norm_mul,markedWithFrozen_norm D hp hg hchar hcop S F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

omit [Fintype ι] in
theorem frozenArgument_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) : frozenArgument hg j F = frozenArgument hg j' F := by
  unfold frozenArgument
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem frozenCore_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j j' : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i = j' i) :
    frozenCore hp hg c j F = frozenCore hp hg c j' F := by
  unfold frozenCore
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem ramifiedBlock_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock hg j F u m = ramifiedBlock hg j' F u m := by
  unfold ramifiedBlock
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

theorem marked_phases_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (R S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg (markedActiveExponent S j) R F u m = sourceRowPhase s hp hg j R F u m ∧
    sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m = sourceSlotPhase s hp hg j S F u m ∧
    sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m = sourceFrozenPhase D s hp hg j F u m := by
  have hj : ∀ i ∈ F, markedActiveExponent S j i = j i := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
    simp only [markedActiveExponent,hn,ite_false]
  simp only [sourceRowPhase,sourceSlotPhase,sourceFrozenPhase,
    frozenArgument_congr hg _ _ F hj,frozenCore_congr hp hg c _ _ F hj,
    ramifiedBlock_congr hg _ _ F hj]
  simp

theorem marked_sourceColumn_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg (markedActiveExponent S j) F u m n b =
      sourceColumn D s hc hg j F u m n b := by
  unfold sourceColumn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
  simp only [markedActiveExponent,hn,ite_false]

theorem mixed_coefficient_hybrid_original_exponents [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      sourceColumn D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hd : Disjoint S F := hF.mono_left Finset.subset_union_right
  have he := mixed_coefficient_hybrid D s hp hc hg hcop hprimary R S F hRS hF hu j hRj hR u m n b hb
  obtain ⟨hr,hs,hf⟩ := marked_phases_eq D s hp hg j R S F hd u m
  rw [hr,hs,hf,marked_sourceColumn_eq D s hc hg j S F hd u m n b] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Family -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase ShortDraftCRT CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem simultaneous_controlled_matrices_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) → SL(2,Eis),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:Eis) ∣ mat x v 0 1 ∧ (3:Eis) ∣ mat x v 1 1-1
        else (3:Eis) ∣ mat x v 0 1+1 ∧ (9:Eis) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  let X := Σ x : α, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ)
  let aa : X → Eis := fun x => (D x.1).matrix x.2 0 0
  let rr : X → Eis := fun x => ∏ i, p x.1 i
  let ss : X → Q := fun x => sector x.1
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  have hacop (x : X) : IsCoprime (aa x) (c*rr x) := by
    refine ⟨(D x.1).matrix x.2 1 1, -(D x.1).matrix x.2 0 1, ?_⟩
    have hd := ((D x.1).matrix x.2).property
    rw [Matrix.det_fin_two] at hd
    change (D x.1).matrix x.2 0 0 * (D x.1).matrix x.2 1 1 -
      (D x.1).matrix x.2 0 1 * (D x.1).matrix x.2 1 0 = 1 at hd
    rw [(D x.1).denominator] at hd
    dsimp [aa,rr]
    linear_combination hd
  have haa (x y : X) (h : ss x = ss y) : N*c ∣ aa x-aa y := by
    dsimp [aa]
    rw [(D x.1).numerator,(D y.1).numerator]
    exact finiteCrossNumerator_fixed_sector N a c ramifiedTraceLambda
      (p x.1) ((D x.1).lift x.2) (p y.1) ((D y.1).lift y.2)
      hcN ((D x.1).lift_period x.2) ((D y.1).lift_period y.2) (hsector x.1 y.1 h)
  have hrr (x y : X) (h : ss x = ss y) : N ∣ rr x-rr y :=
    (dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x.1 y.1 h)
  have hex : ∃ (b d : X → Eis) (C : Q → Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N})),
      (∀ x, aa x*d x-b x*(c*rr x)=1) ∧
      (∀ x, if mode then (9:Eis) ∣ b x ∧ (3:Eis) ∣ d x-1
        else (3:Eis) ∣ b x+1 ∧ (9:Eis) ∣ d x) ∧
      ∀ x, (!![aa x,b x;c*rr x,d x] : Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {N})) = C (ss x) := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_denominator_sector_completions
        N c h9N hbase ss aa rr (fun x => hprimary x.1) hacop
        (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_numerator_sector_completions
        N c hc h9N ss aa rr
        (fun x => (D x.1).numerator_primary h3N (hprimary x.1) hbase x.2)
        (fun x => hprimary x.1) hacop (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
  obtain ⟨b,d,C,hdet,hcond,hmat⟩ := hex
  let mat := fun (x : α) (v : ∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) =>
    controlledCompletionMatrix (aa ⟨x,v⟩) (b ⟨x,v⟩) (c*rr ⟨x,v⟩) (d ⟨x,v⟩) (hdet ⟨x,v⟩)
  refine ⟨mat,fun _ _ => rfl,fun _ _ => rfl,fun x v => hcond ⟨x,v⟩,?_⟩
  intro x y v w hs i j
  have hs' : ss ⟨x,v⟩ = ss ⟨y,w⟩ := hs
  have he := (hmat ⟨x,v⟩).trans ((congrArg C hs').trans (hmat ⟨y,w⟩).symm)
  have he' := congrArg (fun T : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N}) => T i j) he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he')

theorem exists_sector_controlled_arithmetic_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices_dependent
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := fun v i j => hfixed x x v (fun _ => 1) rfl i j
      conditions := hcond x }
  exact ⟨E,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,hfixed⟩

theorem exists_sector_templates {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (κ : Q → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x, (D x).fixedFactor = κ (sector x)) ∧
      ∀ x u m n b,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c hc
            (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
            (s.modelDualNumerator u) u) m n b = β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let A := fun x (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) =>
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc
        (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
        (s.modelDualNumerator u) u) m n b
  have hf : (fun x => (D x).fixedFactor).FactorsThrough sector := by
    intro x y hxy
    exact controlled_fixedFactor_eq (D x) (D y) hN (hprimary x) (hprimary y) hbase
      (hmatrix x y hxy 0 0) (hmatrix x y hxy 0 1)
  have ha : A.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact controlled_static_array_eq (D x) (D y) hc s hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) u m n b
  obtain ⟨κ,hκ⟩ := (Function.factorsThrough_iff _).mp hf
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff A).mp ha
  refine ⟨κ,β,fun x => congrFun hκ x,?_⟩
  intro x u m n b
  exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_ray_templates {α : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (f : Eis) (r P : α → Eis) (hprod : ∀ x, (∏ i, p x i) = f*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x, (E x).fixedFactor = κ (separateSector N (r x) (P x))) ∧
        ∀ x u m n b,
          fixedCuspArrayWithPhase s.index u
            (s.reflectionStaticPhase c hc
              (Ideal.Quotient.mk _ (-((E x).matrix (fun _ => 1) 1 1)*(E x).U))
              (s.modelDualNumerator u) u) m n b = β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N f (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_sector_templates p N a c mode E s hc hN hprimary hbase sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Transport -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Eis}
noncomputable local instance transportFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] [Fintype κ] in
theorem residualWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) :
    residualWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c R F =
      residualWithFrozen hp hg c (R.image f) (F.image f) := by
  unfold residualWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf R i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem markedWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) :
    markedWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c S F =
      markedWithFrozen hp hg c (S.image f) (F.image f) := by
  unfold markedWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf S i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem ramifiedBlock_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S : Finset κ) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock (fun i => hg (f i)) (fun i => j (f i)) S u m =
      ramifiedBlock hg j (S.image f) u m := by
  unfold ramifiedBlock
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem frozenArgument_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenArgument (fun i => hg (f i)) (fun i => j (f i)) F =
      frozenArgument hg j (F.image f) := by
  unfold frozenArgument
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceRowPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) R F u m =
      sourceRowPhase s hp hg j (R.image f) (F.image f) u m := by
  unfold sourceRowPhase
  rw [residualWithFrozen_transport hp hg c f hf R F,
    ramifiedBlock_transport hg (fun _ => 1) f hf R,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceSlotPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) S F u m =
      sourceSlotPhase s hp hg j (S.image f) (F.image f) u m := by
  unfold sourceSlotPhase
  rw [markedWithFrozen_transport hp hg c f hf S F,
    ramifiedBlock_transport hg (fun _ => 0) f hf S,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Functions -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

theorem sourceRowPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg j (R.image f) (F.image f) u m =
      sourceRowPhase s hq hqg j' (R.image g) (F.image g) u m := by
  rw [← sourceRowPhase_transport s hp hg j f hf R F u m,
    ← sourceRowPhase_transport s hq hqg j' g hg' R F u m]
  exact sourceRowPhase_congr_functions s _ _ _ _ _ _ R F u m (funext he) (funext hj)

theorem sourceSlotPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s hp hg j (S.image f) (F.image f) u m =
      sourceSlotPhase s hq hqg j' (S.image g) (F.image g) u m := by
  rw [← sourceSlotPhase_transport s hp hg j f hf S F u m,
    ← sourceSlotPhase_transport s hq hqg j' g hg' S F u m]
  exact sourceSlotPhase_congr_functions s _ _ _ _ _ _ S F u m (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SectorIndependence -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance sectorIndependentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

lemma frozenCore_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (c : Eis) (j j' : κ → ℕ) (F : Finset κ) (he : p=q) (hj : j=j') :
    frozenCore hp hg c j F = frozenCore hq hqg c j' F := by
  subst q; subst j'; rfl

lemma ramifiedBlock_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    ramifiedBlock hg j F u m = ramifiedBlock hqg j' F u m := by
  subst q; subst j'; rfl

def frozenColumnProduct {κ : Type*} [Fintype κ]
    {p : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) : ℂ :=
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

theorem frozenColumnProduct_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) (n b : Ideal Eis) :
    frozenColumnProduct (fun i => hg (f i)) (fun i => j (f i)) F n b =
      frozenColumnProduct hg j (F.image f) n b := by
  unfold frozenColumnProduct
  rw [Finset.prod_image hf.injOn]

lemma frozenColumnProduct_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) (he : p=q) (hj : j=j') :
    frozenColumnProduct hg j F n b = frozenColumnProduct hqg j' F n b := by
  subst q; subst j'; rfl

theorem sourceFrozenPhase_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1) (hr₀ : λ₀^2 ∣ (∏ i, q i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hmatrix : ∀ i j, N ∣ D.matrix (fun _ => 1) i j-D₀.matrix (fun _ => 1) i j)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s hp hg j (F.image f) u m =
      sourceFrozenPhase D₀ s hq hqg j' (F.image g) u m := by
  unfold sourceFrozenPhase
  rw [controlled_fixedFactor_eq D D₀ hN hr hr₀ hbase (hmatrix 0 0) (hmatrix 0 1),
    ← frozenCore_transport hp hg c j f hf F,← frozenCore_transport hq hqg c j' g hg' F,
    ← ramifiedBlock_transport hg j f hf F,← ramifiedBlock_transport hqg j' g hg' F,
    frozenCore_congr_functions _ _ _ _ c _ _ F (funext he) (funext hj),
    ramifiedBlock_congr_functions _ _ _ _ F _ _ (funext he) (funext hj)]

theorem sourceColumn_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hbad : CubicEisenstein.ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, q i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1-D₀.matrix (fun _ => 1) 1 1)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg j (F.image f) u m n b =
      sourceColumn D₀ s hc hqg j' (F.image g) u m n b := by
  unfold sourceColumn
  rw [controlled_static_array_eq D D₀ hc s hbad hr hd u m n b]
  congr 1
  change frozenColumnProduct hg j (F.image f) n b = frozenColumnProduct hqg j' (F.image g) n b
  rw [← frozenColumnProduct_transport hg j f hf F,← frozenColumnProduct_transport hqg j' g hg' F]
  exact frozenColumnProduct_congr_functions _ _ _ _ F n b (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Common -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_common_reflected_coefficients {α Q κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (γ : Q → Eisˣ → ℕ → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x u m, sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
        γ (sector x) u m) ∧
      ∀ x u m n b, sourceColumn (D x) s hc (hg x) (j x) (F.image (f x)) u m n b =
        β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let G := fun x => sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x))
  let B := fun x => sourceColumn (D x) s hc (hg x) (j x) (F.image (f x))
  have hG : G.FactorsThrough sector := by
    intro x y hxy
    funext u m
    exact sourceFrozenPhase_sector_independent (D x) (D y) s (hp x) (hg x) (hp y) (hg y)
      hN (hprimary x) (hprimary y) hbase (hmatrix x y hxy) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m
  have hB : B.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact sourceColumn_sector_independent (D x) (D y) s hc (hg x) (hg y) hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m n b
  obtain ⟨γ,hγ⟩ := (Function.factorsThrough_iff G).mp hG
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff B).mp hB
  refine ⟨γ,β,?_,?_⟩
  · intro x u m
    exact congrFun (congrFun (congrFun hγ x) u) m
  · intro x u m n b
    exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedProduct : Eis) (r P : α → Eis)
    (hprod : ∀ x, (∏ i, p x i) = fixedProduct*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧ (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧ (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
          γ (separateSector N (r x) (P x)) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (hg x) (j x) (F.image (f x)) u m n b =
          β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N fixedProduct (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_common_reflected_coefficients p N a c mode E s hp hc hg hN hprimary hbase
    j f hf hfixed hjfixed F sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Canonical -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure PrimeFamily (ι : Type*) where
  ideal : ι → Ideal Eis
  maximal : ∀ i, (ideal i).IsMaximal
  good : ∀ i, λ₀ ∉ ideal i

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)
instance idealMaximal (i : ι) : (G.ideal i).IsMaximal := G.maximal i

def generator (i : ι) : Eis := primaryPrime (G.ideal i)

lemma generator_ne_zero (i : ι) : G.generator i ≠ 0 := primaryPrime_ne_zero _ (G.good i)
lemma generator_span (i : ι) : Ideal.span {G.generator i} = G.ideal i :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.1
lemma generator_primary (i : ι) : λ₀^2 ∣ G.generator i-1 :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.2
instance generatorMaximal (i : ι) : (Ideal.span {G.generator i}).IsMaximal :=
  G.generator_span i ▸ G.maximal i
lemma generator_good (i : ι) : λ₀ ∉ Ideal.span {G.generator i} := by
  rw [G.generator_span]
  exact G.good i

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

lemma generator_product_primary [Fintype ι] : λ₀^2 ∣ (∏ i, G.generator i)-1 :=
  primary_finset_product Finset.univ G.generator (fun i _ => G.generator_primary i)

lemma generator_coprime_period (N : Eis)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) (i : ι) :
    IsCoprime N (G.generator i) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [G.generator_span]
  exact hN i

lemma generator_product_coprime_period [Fintype ι] (N c : Eis) (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

theorem exists_controlled [Fintype ι] (N a c : Eis) (mode : Bool)
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime G.ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    Nonempty (ControlledStratumArithmetic G.generator N a c mode) := by
  apply exists_controlledStratumArithmetic G.generator G.generator_ne_zero
  · intro i k hik
    simpa only [G.generator_span] using hcop hik
  · exact G.generator_primary
  · exact hc
  · exact hN
  · exact hbase
  · exact hac
  · exact G.generator_coprime_period N hNp

end PrimeFamily

theorem canonical_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, (G x).ideal (f x i)=(G y).ideal (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (G x).generator_ne_zero (G x).generator_good
          (j x) (F.image (f x)) u m =
          γ (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (G x).generator_good (j x) (F.image (f x)) u m n b =
          β (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,γ,β,hγ,hβ⟩ := exists_separate_common_reflected_coefficients
    (fun x => (G x).generator) N a c mode D s (fun x => (G x).generator_ne_zero) hc
    (fun x => (G x).generator_good) hN (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    j f hf (fun x y i => congrArg primaryPrime (hfixed x y i)) hjfixed F
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x)) (fun x => primaryGenerator (slot x)) hproduct
  exact ⟨E,γ,β,hγ,hβ⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Rows -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

def sum (G : PrimeFamily ι) (H : PrimeFamily κ) : PrimeFamily (ι ⊕ κ) where
  ideal := Sum.elim G.ideal H.ideal
  maximal i := by cases i with | inl i => exact G.maximal i | inr i => exact H.maximal i
  good i := by cases i with | inl i => exact G.good i | inr i => exact H.good i

lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))

def residual (K : Ideal Eis) (hK : Admissible K) : PrimeFamily (PrimeIndex K) where
  ideal := fun P => P.val
  maximal _P := inferInstance
  good := admissiblePrimeGood K hK

lemma residual_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P, (residual K hK).ideal P) = K := admissible_primeIndex_product K hK

lemma residual_dvd (K : Ideal Eis) (hK : Admissible K) (P : PrimeIndex K) : P.val ∣ K :=
  Ideal.dvd_iff_le.mpr (primeIndex_le K hK.1 P)

lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)

def reflected {φ σ : Type*} (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) : PrimeFamily (φ ⊕ (PrimeIndex K ⊕ σ)) := F.sum ((residual K hK).sum S)

lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring

lemma reflected_pairwise {φ σ : Type*} [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hKS : IsCoprime K (∏ i, S.ideal i))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hFS : ∀ f i, IsCoprime (F.ideal f) (S.ideal i)) :
    Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal) := by
  apply sum_pairwise F _ hF
  · apply sum_pairwise _ S (residual_pairwise K hK) hS
    intro P i
    exact (hKS.of_isCoprime_of_dvd_left (residual_dvd K hK P)).of_isCoprime_of_dvd_right
      (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ i))
  · intro f i
    cases i with
    | inl P => exact (hFK f).of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hFS f i

lemma reflected_period {φ σ : Type*}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (N : Eis)
    (hF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hK' : IsCoprime (Ideal.span {N}) K)
    (hS : ∀ i, IsCoprime (Ideal.span {N}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {N}) ((F.reflected K hK S).ideal i) := by
  intro i
  cases i with
  | inl f => exact hF f
  | inr i => cases i with
    | inl P => exact hK'.of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hS i

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Moving -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectedExponent {φ ρ σ : Type*} (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ : Type*) [Fintype φ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ : Type*) [Fintype ρ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ : Type*) [Fintype σ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

lemma reflected_indices_partition (φ ρ σ : Type*) [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  constructor
  · rintro i ⟨r, rfl⟩ ⟨s, h⟩
    cases h
  constructor
  · rintro i (⟨r, rfl⟩ | ⟨s, rfl⟩) ⟨f, h⟩ <;> cases h
  · ext i
    cases i with
    | inl f => simp
    | inr i => cases i with
      | inl r => simp
      | inr s => simp

lemma reflected_residual_exponent {φ ρ σ : Type*} [Fintype ρ] (jF : φ → ℕ) :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
lemma reflected_residual_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl
end PrimeFamily

theorem moving_common_reflected_coefficients {α φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : α → Ideal Eis) (hK : ∀ x, Admissible (K x))
    (S : α → PrimeFamily σ) (jF : φ → ℕ)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1
      else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : ∀ x, Pairwise (Function.onFun IsCoprime (S x).ideal))
    (hKS : ∀ x, IsCoprime (K x) (∏ i, (S x).ideal i))
    (hFK : ∀ x f, IsCoprime (F.ideal f) (K x))
    (hFS : ∀ x f i, IsCoprime (F.ideal f) ((S x).ideal i))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : ∀ x, IsCoprime (Ideal.span {N}) (K x))
    (hNS : ∀ x i, IsCoprime (Ideal.span {N}) ((S x).ideal i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (F.reflected (K x) (hK x) (S x)).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s
          (F.reflected (K x) (hK x) (S x)).generator_ne_zero
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m =
          γ (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m n b =
          β (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m n b := by
  classical
  simpa only [frozenIndices] using canonical_common_reflected_coefficients
    (fun x => F.reflected (K x) (hK x) (S x)) N a c mode s hc hN hbase hac
    (fun x => F.reflected_pairwise (K x) (hK x) (S x) hF (hS x) (hKS x) (hFK x) (hFS x))
    (fun x => F.reflected_period (K x) (hK x) (S x) N hNF (hNK x) (hNS x))
    (fun _ => reflectedExponent jF) (fun _ => Sum.inl) (fun _ => Sum.inl_injective)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) Finset.univ (∏ i, F.ideal i) K
    (fun x => ∏ i, (S x).ideal i) (fun x => F.reflected_product (K x) (hK x) (S x))

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Projections -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

def actualRowPhase (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceRowPhase s (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good (Sum.elim jF (fun _ => 1))
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

def actualSlotPhase (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceSlotPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
    (Sum.elim jF (fun _ => 0)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

omit [Fintype σ] in
theorem sourceRowPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (residualIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualRowPhase F K hK jF s u m := by
  classical
  let f : φ ⊕ PrimeIndex K → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceRowPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) =
      (F.sum (PrimeFamily.residual K hK)).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 1) := by
    funext i
    cases i <;> rfl
  have hh := sourceRowPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualRowPhase,residualIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

theorem sourceSlotPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualSlotPhase F S jF s u m := by
  classical
  let f : φ ⊕ σ → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceSlotPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) = (F.sum S).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 0) := by
    funext i
    cases i <;> rfl
  have hh := sourceSlotPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum S).generator_ne_zero (F.sum S).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualSlotPhase,slotIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Actual -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualMixedCoefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  s.amplitude u m n b *
    (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
      (s.modelDualNumerator u m n b)) *
    ∏ i, mixedActiveBracket (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) D i (s.modelDualNumerator u m n b)

theorem actualMixedCoefficient_factor (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*actualSlotPhase F S jF s u m*
        sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
          (F.reflected K hK S).generator_good (reflectedExponent jF)
          (frozenIndices φ (PrimeIndex K) σ) u m)*
      sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
        (frozenIndices φ (PrimeIndex K) σ) u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
      quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
      (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
      (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  obtain ⟨hRS,hF,hu⟩ := reflected_indices_partition φ (PrimeIndex K) σ
  have hF' : Disjoint (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ)
      (frozenIndices φ (PrimeIndex K) σ) := by
    simpa only [Finset.disjoint_left,Finset.mem_union] using hF
  have hu' : (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ) ∪
      frozenIndices φ (PrimeIndex K) σ = Finset.univ := by
    simpa only [Finset.ext_iff,Finset.mem_union] using hu
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.reflected K hK S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hr : Admissible (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) := by
    rw [F.reflected_residual_product K hK S]
    exact hK
  have he := mixed_coefficient_hybrid_original_exponents D s
    (F.reflected K hK S).generator_ne_zero hc (F.reflected K hK S).generator_good hcp
    (F.reflected K hK S).generator_primary _ _ _ hRS hF' hu'
    (reflectedExponent jF) (reflected_residual_exponent jF) hr u m n b hb
  have hcard : (slotIndices φ (PrimeIndex K) σ).card = Fintype.card σ := by
    rw [slotIndices,Finset.card_image_of_injective _ (Sum.inr_injective.comp Sum.inr_injective)]
    rfl
  rw [hcard,sourceRowPhase_eq_actual,sourceSlotPhase_eq_actual,
    F.reflected_residual_product K hK S,F.reflected_slot_product K hK S] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Columns -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}

def actualCuspColumn (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b

lemma actualCuspColumn_norm_le_one (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ‖actualCuspColumn D s hc u m n b‖ ≤ 1 :=
  fixedCuspArrayWithPhase_norm_le_one s.index u _
    (s.reflectionStaticPhase_norm_le_one c hc _ _ u) m n b

def frozenBranchColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  A n b * reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
    (primaryGenerator n) (primaryGenerator b)

def frozenExtracted (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun i => Ideal.span {F.generator i}) jF e v

def frozenBranchScale (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) : ℝ :=
  Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ)

theorem sourceColumn_eq_sum_frozenBranches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m n b =
      ∑ e : φ → Fin 3, frozenBranchColumn F jF e (actualCuspColumn D s hc u m) n b := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceColumn frozenIndices
  rw [Finset.prod_image Sum.inl_injective.injOn]
  change actualCuspColumn D s hc u m n b *
    (∏ i, bracket (actualSextic (Ideal.span {F.generator i}) (F.generator_good i)) (jF i)
      (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))) = _
  exact (congrArg (actualCuspColumn D s hc u m n b * ·)
    (prod_bracket_eq_full_branches (fun i => Ideal.span {F.generator i}) F.generator_good
      jF (primaryGenerator n) (primaryGenerator b))).trans (Finset.mul_sum _ _ _)

theorem frozenBranchColumn_norm_le (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e A n b‖ ≤ frozenBranchScale F jF e := by
  rw [frozenBranchColumn,norm_mul]
  calc
    _ ≤ 1*‖reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
        (primaryGenerator n) (primaryGenerator b)‖ := mul_le_mul_of_nonneg_right (hA n b) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact reflectedBranch_norm_bound _ F.generator_good jF e _ _

theorem frozenBranchColumn_normalized_bound (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1)
    (n b : Ideal Eis) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖frozenBranchColumn F jF e A n b‖ /
      (Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
        (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  apply (div_le_div_of_nonneg_right ?_ (by positivity)).trans
    (reflectedBranch_normalized_bound (fun i => Ideal.span {F.generator i}) F.generator_good
      jF e (primaryGenerator n) (primaryGenerator b) U B hU hB)
  rw [frozenBranchColumn,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hA n b)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.BoundedTemplates -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def boundedExtension (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then z else 0
lemma boundedExtension_norm (z : ℂ) : ‖boundedExtension z‖ ≤ 1 := by
  unfold boundedExtension
  split_ifs with h
  · exact h
  · simp
lemma boundedExtension_eq (z : ℂ) (hz : ‖z‖ ≤ 1) : boundedExtension z = z := ite_eq_left hz

theorem canonical_bounded_cusp_templates {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator (row x))
          (primaryGenerator (slot x)))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,κ,A,hκ,hA⟩ := exists_separate_ray_templates
    (fun x => (G x).generator) N a c mode D s hc hN
    (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x))
    (fun x => primaryGenerator (slot x)) hproduct
  refine ⟨E,fun q => boundedExtension (κ q),fun q u m n b => boundedExtension (A q u m n b),
    fun q => boundedExtension_norm _,fun q u m n b => boundedExtension_norm _,?_,?_⟩
  · intro x
    change (E x).fixedFactor = boundedExtension _
    rw [← hκ x,boundedExtension_eq _ ((E x).fixedFactor_norm hN
      (G x).generator_product_primary hbase).le]
  · intro x u m n b
    change actualCuspColumn (E x) s hc u m n b = boundedExtension _
    rw [← hA x u m n b]
    exact (boundedExtension_eq _ (actualCuspColumn_norm_le_one (E x) s hc u m n b)).symm

theorem common_frozen_branch_bound {φ Q : Type*} [Fintype φ]
    (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ q u m n b, ‖A q u m n b‖ ≤ 1) (q : Q) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e (A q u m) n b‖ ≤ frozenBranchScale F jF e :=
  frozenBranchColumn_norm_le F jF e (A q u m) (hA q u m) n b

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FrozenNorms -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} {p : ι → Eis} {N a c : Eis} {mode : Bool}

lemma frozenCofactorCharacter_cross_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (p k)‖ = 1 := by
  have hn := crossSymbol_norm hg hcop i k hik
  unfold frozenCofactorCharacter
  split_ifs
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv',norm_pow,norm_inv]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖⁻¹^2 = 1
    rw [hn]; norm_num
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0),norm_pow]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖^(2*j+2) = 1
    rw [hn,one_pow]

lemma frozenCofactorCharacter_product_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (S : Finset ι) (hi : i ∉ S) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (∏ k ∈ S, p k)‖ = 1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact frozenCofactorCharacter_cross_norm hg hcop i k (fun h => hi (h ▸ hk)) j

variable [Fintype ι]

lemma frozenPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (j : ℕ) (hj : j < 6) : ‖frozenPrimeScalar (p i) c (hp i) (hg i) j‖ = 1 := by
  have hh := local_phase_norm D hp hg hchar i j hj
  rw [controlled_frozen_phase,norm_mul] at hh
  have hn : ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i)‖ = 1 := by
    exact frozenCofactorCharacter_product_norm hg hcop i (Finset.univ.erase i) (by simp) j
  simpa only [hn,mul_one] using hh

lemma frozenCore_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) : ‖frozenCore hp hg c j F‖ = 1 := by
  rw [frozenCore,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_mul,frozenPrimeScalar_norm D hp hg hchar hcop i (j i) (hj i hi),one_mul]
  exact frozenCofactorCharacter_product_norm hg hcop i (F.erase i) (by simp) (j i)

lemma sourceFrozenPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) (u : Eisˣ) (m : ℕ) :
    ‖sourceFrozenPhase D s hp hg j F u m‖ = 1 := by
  rw [sourceFrozenPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    frozenCore_norm D hp hg hchar hcop j F hj,ramifiedBlock_norm]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualFrozenPhase (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  star κ * frozenCore F.generator_ne_zero F.generator_good c jF Finset.univ *
    ramifiedBlock F.generator_good jF Finset.univ
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

lemma sourceFrozenPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m = actualFrozenPhase F jF D.fixedFactor s u m := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceFrozenPhase frozenIndices
  rw [← frozenCore_transport (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good c (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ,
    ← ramifiedBlock_transport (F.reflected K hK S).generator_good
      (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ]
  rfl

lemma frozenExtracted_ne_zero (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v ≠ 0 := by
  apply reflectionExtractedDivisor_ne_zero
  intro i
  rw [F.generator_span]
  exact NeZero.ne _

lemma frozenBranchScale_pos (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) :
    0 < frozenBranchScale F jF e := by
  have hn (v : Fin 3) : (0:ℝ) < Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (hn 1)) (Real.sqrt_pos.mpr (hn 2)))
    (Real.sqrt_pos.mpr (hn 0))

def normalizedFrozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  (frozenBranchScale F jF e : ℂ)⁻¹ * frozenBranchColumn F jF e A n b

lemma normalizedFrozenColumn_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖normalizedFrozenColumn F jF e A n b‖ ≤ 1 := by
  have hp := frozenBranchScale_pos F jF e
  rw [normalizedFrozenColumn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  calc
    _ ≤ (frozenBranchScale F jF e)⁻¹*frozenBranchScale F jF e :=
      mul_le_mul_of_nonneg_left (frozenBranchColumn_norm_le F jF e A hA n b) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma frozenBranchColumn_eq_normalized (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e A n b =
      (frozenBranchScale F jF e : ℂ)*normalizedFrozenColumn F jF e A n b := by
  rw [normalizedFrozenColumn,← mul_assoc,mul_inv_cancel₀,one_mul]
  exact_mod_cast (frozenBranchScale_pos F jF e).ne'

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ActualBounds -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma two_block_phase_bounds (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime (F.sum S).ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum S).ideal i))
    (hchar : ∀ i, ringChar (Eis ⧸ (F.sum S).ideal i) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
      (Sum.elim jF (fun _ => 1)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m‖ ≤ 1 ∧
    ‖actualSlotPhase F S jF s u m‖ ≤ 1 := by
  classical
  obtain ⟨D⟩ := (F.sum S).exists_controlled N a c mode hc hN hbase hac hcop hNp
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.sum S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {(F.sum S).generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) ((F.sum S).generator_span i)
    exact he.symm ▸ hchar i
  have hd : Disjoint (Finset.univ.image (Sum.inr : σ → φ ⊕ σ)) (Finset.univ.image Sum.inl) := by
    simp only [Finset.disjoint_left,Finset.mem_image,Finset.mem_univ,true_and]
    rintro i ⟨k,rfl⟩ ⟨f,h⟩
    cases h
  exact ⟨sourceRowPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m,
    sourceSlotPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m⟩

lemma actualRowPhase_norm_le_one (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (jF : φ → ℕ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : IsCoprime (Ideal.span {N}) K)
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖actualRowPhase F K hK jF s u m‖ ≤ 1 := by
  have hcp := PrimeFamily.sum_pairwise F (PrimeFamily.residual K hK) hF
    (PrimeFamily.residual_pairwise K hK) (fun f P =>
      (hFK f).of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P))
  have hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (PrimeFamily.residual K hK)).ideal i) := by
    intro i
    cases i with
    | inl f => exact hNF f
    | inr P => exact hNK.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P)
  have hchar : ∀ i, ringChar (Eis ⧸ (F.sum (PrimeFamily.residual K hK)).ideal i) ≠ 2 := by
    intro i
    cases i with
    | inl f => exact hcharF f
    | inr P => exact (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).2
  have hh := (two_block_phase_bounds F (PrimeFamily.residual K hK) jF s hc hN hbase hac hcp hNp hchar u m).1
  unfold actualRowPhase
  convert hh using 1 ; congr 2 <;> ext i <;> simp

lemma actualFrozenPhase_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ) (hκ : ‖κ‖ ≤ 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (hj : ∀ f, jF f < 6) (u : Eisˣ) (m : ℕ) :
    ‖actualFrozenPhase F jF κ s u m‖ ≤ 1 := by
  obtain ⟨D⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  have hcp : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {F.generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) (F.generator_span i)
    exact he.symm ▸ hcharF i
  rw [actualFrozenPhase,norm_mul,norm_mul,norm_star,
    frozenCore_norm D _ _ hch hcp _ _ (fun i _ => hj i),ramifiedBlock_norm,mul_one,mul_one]
  exact hκ

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actualMixedCoefficient_common_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (κ : ℂ) (A : Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : D.fixedFactor = κ)
    (hA : ∀ u m n b, actualCuspColumn D s hc u m n b = A u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*
          actualSlotPhase F S jF s u m*actualFrozenPhase F jF κ s u m)*
        (frozenBranchScale F jF e:ℂ)*normalizedFrozenColumn F jF e (A u m) n b*
        (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
        (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
        (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  rw [actualMixedCoefficient_factor F K hK S jF D s hc hcop u m n b hb,
    sourceFrozenPhase_eq_actual,hκ,sourceColumn_eq_sum_frozenBranches]
  have hfun : actualCuspColumn D s hc u m = A u m := funext (fun n => funext (fun b => hA u m n b))
  rw [hfun,Finset.mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [frozenBranchColumn_eq_normalized]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

