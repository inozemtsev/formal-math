module

public import Green64.Library.Correlation.Part062
public import Green64.Library.Correlation.UnfilteredRootVacuumFinite
public import Green64.Library.Weights.Part093
public import Mathlib.Data.Real.Sqrt
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Green64.Library.Weights.Part094

@[expose] public section

/-!
# Correlation / Part064

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredRootFunctionalRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The original coherent boundary, with its exact redundant initial ND
mask inserted before any forest edge is discarded. -/
def sourceOriginalRootFunctionalRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (test : List (Option ℕ) → ℂ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N:ℂ)*
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y:ℂ)*
      star (physicalVacuum SP sm BP bm J ell y)*
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T
          (fun out H' => test H' * physicalVacuum SP sm BP bm J ell out) N 0 y
          ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)
       else 0)

theorem source_original_root_INITIAL_PAD_LENGTH434 (Y : Output) :
    ((physicalOutputInitialBirths SP sm BP bm J ell Y).map some).length =
      Fintype.card BG*(J+ell) := by
  simp [physicalOutputInitialBirths,List.length_flatMap]

theorem source_original_root_FUNCTIONAL_ROOT_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (fun H => if (H.filterMap id).Nodup then 1 else 0) =
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  rw [←source_original_root_PADDED_ROOT_EXACT434]
  unfold sourceOriginalRootFunctionalRoot434 sourceOriginalRootPaddedRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  have hf : (fun (out : Output) (H : List (Option ℕ)) =>
      (if (H.filterMap id).Nodup then (1:ℂ) else 0) * physicalVacuum SP sm BP bm J ell out) =
      (fun out H => if (H.filterMap id).Nodup then physicalVacuum SP sm BP bm J ell out else 0) := by
    funext out H
    split_ifs <;> simp
  rw [hf,source_original_root_FUNCTIONAL_NODUP_EXACT434]
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · rw [if_pos hn]
  · rw [if_neg hn,source_original_root_PADDED_CHAIN_EXACT434,
      source_original_forest_LISTED_CHAIN_EXACT434]
    simp [hn]

/-- The conjugation is necessary: star(initialKet) carries the positive
initial phase in the literal complex-bilinear scalar. -/
def sourceOriginalRootInitialKet434 (phi : ℕ → Option ℕ → ℂ) (Y : Output) : ℂ :=
  if (physicalOutputInitialBirths SP sm BP bm J ell Y).Nodup then
    star (sourceOriginalRootListPhase434 phi 0
      ((physicalOutputInitialBirths SP sm BP bm J ell Y).map some)) *
      physicalVacuum SP sm BP bm J ell Y else 0

/-- Exact coherent pairing for every fixed slot-phase family. No phase
is pulled through an orbit conditional mean. -/
theorem source_original_root_FUNCTIONAL_PHASE_PAIR434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (phi : ℕ → Option ℕ → ℂ) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListPhase434 phi 0) =
    (physicalSourceBaselineProduct BP bm q (2*R):ℂ) *
      physicalSymmetricInner SP sm BP bm (J+ell) cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V)
        (sourceOriginalRootInitialKet434 SP sm BP bm J ell phi)
        (sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T phi (physicalVacuum SP sm BP bm J ell)
          (2*R) 0 (Fintype.card BG*(J+ell))) := by
  unfold sourceOriginalRootFunctionalRoot434 physicalSymmetricInner
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [source_original_root_ACTUAL_PHASE_CHAIN434,source_original_root_INITIAL_PAD_LENGTH434]
  unfold sourceOriginalRootInitialKet434
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn,star_mul,star_star]
    ring
  · simp only [if_neg hn,star_zero,mul_zero,zero_mul]

theorem source_original_root_INITIAL_KET_ENERGY434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (phi : ℕ → Option ℕ → ℂ) (hphi : ∀ i a,‖phi i a‖=1) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalRootInitialKet434 SP sm BP bm J ell phi) ≤
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalVacuum SP sm BP bm J ell) := by
  unfold sourceOriginalUnfilteredIdealOrbitEnergy434
  apply Finset.sum_le_sum
  intro Y hY
  unfold sourceOriginalRootInitialKet434
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell Y).Nodup
  · simp only [if_pos hn,norm_mul,norm_star,
      source_original_root_LIST_PHASE_UNIT434 phi hphi,one_mul,le_refl]
  · simp only [if_neg hn,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
    exact mul_nonneg (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu Y hY).le
      (sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualAlphabet -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sourceOriginalRootValid434 (S : Finset ℕ) (H : List (Option ℕ)) : Prop :=
  ∀ p,some p∈H → p∈S

theorem source_original_root_VALID_APPEND434
    (S : Finset ℕ) (H B : List (Option ℕ))
    (hH : sourceOriginalRootValid434 S H) (hB : sourceOriginalRootValid434 S B) :
    sourceOriginalRootValid434 S (H++B) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hH p hp
  · exact hB p hp

theorem source_original_root_VALID_GET434
    (S : Finset ℕ) (H : List (Option ℕ)) (hH : sourceOriginalRootValid434 S H)
    (i p : ℕ) (hi : i<H.length) (hp : H.getD i none=some p) : p∈S := by
  apply hH
  rw [List.getD_eq_getElem H none hi] at hp
  rw [←hp]
  exact List.getElem_mem hi

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The finite NUMERICAL alphabet is the union of actual BIG moduli;
equal numeric values are identified even across different groups. -/
def sourceOriginalRootActualAlphabet434 : Finset ℕ :=
  Finset.univ.biUnion (fun g : BG => Finset.univ.image (bm g))

theorem source_original_root_ACTUAL_ALPHABET_MEMBER434 (g : BG) (p : BP g) :
    bm g p∈sourceOriginalRootActualAlphabet434 BP bm := by
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

theorem source_original_root_G_PAD_VALID434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) :
    sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm)
      (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z) := by
  intro p hp
  rcases List.mem_flatMap.mp hp with ⟨g,hg,hp⟩
  rcases List.mem_ofFn.mp hp with ⟨i,hi⟩
  by_cases hn : i.val<(z g).2.1.val
  · have he : bm g ((z g).2.2 ⟨i.val,hn⟩).1=p := by
      simpa only [sourceOriginalRootPadPrefix434,dif_pos hn,Option.some.injEq] using hi
    rw [←he]
    exact source_original_root_ACTUAL_ALPHABET_MEMBER434 BP bm _ _
  · simp [sourceOriginalRootPadPrefix434,hn] at hi

theorem source_original_root_E_PAD_VALID434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm)
      (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z) := by
  intro p hp
  rcases List.mem_flatMap.mp hp with ⟨g,hg,hp⟩
  rcases List.mem_map.mp hp with ⟨i,hi,he⟩
  unfold sourceOriginalRootELabel434 at he
  split_ifs at he with hf
  · have hh := Option.some.inj he
    rw [←hh]
    exact source_original_root_ACTUAL_ALPHABET_MEMBER434 BP bm _ _

theorem source_original_root_INITIAL_VALID434 (Y : Output) :
    sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm)
      ((physicalOutputInitialBirths SP sm BP bm J ell Y).map some) := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨p',hp',he⟩
  have hpp : p'=p := Option.some.inj he
  subst p'
  rcases List.mem_flatMap.mp hp' with ⟨g,hg,hp'⟩
  rcases List.mem_map.mp hp' with ⟨i,hi,he⟩
  rw [←he]
  exact source_original_root_ACTUAL_ALPHABET_MEMBER434 BP bm _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootBoundary -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Finite positive-density Cauchy--Schwarz. No normalization of the
physical support, vacuum mass or orbit density is used. -/
theorem source_original_root_WEIGHTED_CS434
    {I : Type} (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i)
    (f g : I → ℂ) :
    ‖∑ i∈s,(w i:ℂ)*star (f i)*g i‖ ≤
      Real.sqrt (∑ i∈s,w i*‖f i‖^2)*Real.sqrt (∑ i∈s,w i*‖g i‖^2) := by
  have hf : (∑ i∈s,(Real.sqrt (w i)*‖f i‖)^2) = ∑ i∈s,w i*‖f i‖^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,Real.sq_sqrt (hw i hi)]
  have hg : (∑ i∈s,(Real.sqrt (w i)*‖g i‖)^2) = ∑ i∈s,w i*‖g i‖^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,Real.sq_sqrt (hw i hi)]
  calc
    _ ≤ ∑ i∈s,‖(w i:ℂ)*star (f i)*g i‖ := norm_sum_le _ _
    _ = ∑ i∈s,(Real.sqrt (w i)*‖f i‖)*(Real.sqrt (w i)*‖g i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i hi)]
      calc
        _ = (Real.sqrt (w i))^2*‖f i‖*‖g i‖ := by rw [Real.sq_sqrt (hw i hi)]
        _ = _ := by ring
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt s
        (fun i => Real.sqrt (w i)*‖f i‖) (fun i => Real.sqrt (w i)*‖g i‖)
      rw [hf,hg] at h
      exact h

theorem source_original_root_WEIGHTED_CS_BUDGET434
    {I : Type} (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i)
    (f g : I → ℂ) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf : (∑ i∈s,w i*‖f i‖^2) ≤ B)
    (hg : (∑ i∈s,w i*‖g i‖^2) ≤ K^2*B) :
    ‖∑ i∈s,(w i:ℂ)*star (f i)*g i‖ ≤ K*B := by
  apply (source_original_root_WEIGHTED_CS434 s w hw f g).trans
  calc
    _ ≤ Real.sqrt B*Real.sqrt (K^2*B) :=
      mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K*B := by
      rw [Real.sqrt_mul (sq_nonneg K),Real.sqrt_sq_eq_abs,abs_of_nonneg hK]
      nlinarith [Real.sq_sqrt hB]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Boundary assembly for an independently supplied phased-chain energy
estimate. It pays the whole vacuum mass ONCE. This conditional adapter
does not itself assert a chain/operator/root saving. -/
theorem source_original_root_PHASE_BOUNDARY434
    (q rho : ℝ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p)
    (phi : ℕ → Option ℕ → ℂ) (hphi : ∀ i a,‖phi i a‖=1)
    (B : ℝ) (hB : 0 ≤ B)
    (hchain :
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V)
        (sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T phi (physicalVacuum SP sm BP bm J ell)
          (2*R) 0 (Fintype.card BG*(J+ell))) ≤
      B^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V) (physicalVacuum SP sm BP bm J ell)) :
    ‖sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListPhase434 phi 0)‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      (B*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V) (physicalVacuum SP sm BP bm J ell)) := by
  rw [source_original_root_FUNCTIONAL_PHASE_PAIR434,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply source_original_root_WEIGHTED_CS_BUDGET434
    (physicalFockOrbitSupport SP sm BP bm (J+ell) cap)
    (physicalOrbitMass SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm q (2*R) V))
    (fun Y hY => (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs
      (physicalSourceMuTilde BP bm q (2*R) V) hVs hmu Y hY).le)
  · unfold sourceOriginalUnfilteredIdealOrbitEnergy434
    exact Finset.sum_nonneg (fun Y hY => mul_nonneg
      (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V) hVs hmu Y hY).le (sq_nonneg _))
  · exact hB
  · exact source_original_root_INITIAL_KET_ENERGY434 SP sm BP bm J ell cap
      Vs hVs (physicalSourceMuTilde BP bm q (2*R) V) hmu phi hphi
  · exact hchain
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


theorem source_original_root_FUNCTIONAL_ROOT_SUM434
    {I : Type} [Fintype I]
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (test : I → List (Option ℕ) → ℂ) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (fun H => ∑ a : I,test a H) =
    ∑ a : I,sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (test a) := by
  unfold sourceOriginalRootFunctionalRoot434
  dsimp only
  simp_rw [Finset.sum_mul,source_original_root_FUNCTIONAL_SUM434]
  have hm (P : Prop) [Decidable P] (f : I → ℂ) :
      (if P then ∑ a : I,f a else 0)=∑ a : I,if P then f a else 0 := by
    by_cases hp : P <;> simp [hp]
  simp_rw [hm,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem source_original_root_FUNCTIONAL_ROOT_CONGR_LENGTH434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (test test' : List (Option ℕ) → ℂ)
    (heq : ∀ H,H.length=Fintype.card BG*(J+ell)+(2*R+1)*(Fintype.card BG*T)+
      (2*R)*(Fintype.card BG*(J+ell)) → test H=test' H) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T test =
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T test' := by
  unfold sourceOriginalRootFunctionalRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell Y).Nodup
  · rw [if_pos hn,if_pos hn]
    congr 1
    apply source_original_root_FUNCTIONAL_CONGR_LENGTH434
      SP sm BP bm J ell m cap patterns
    intro Y' H' hH'
    rw [source_original_root_INITIAL_PAD_LENGTH434] at hH'
    rw [heq H' hH']
  · rw [if_neg hn,if_neg hn]

/-- Exact signed increasing-forest expansion of the EXISTING projected
source root, with original coefficients, initial ND, all local ND masks,
both OLD gates, independent representative averaging and final G/vacuum. -/
theorem source_original_root_ORIGINAL_FOREST_SUM434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    let A := (2*R+1)*Fintype.card BG*(J+ell+T)
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    ∑ p : SourceOriginalRootForest434 A,
      sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T (sourceOriginalRootListForestTerm434 p) := by
  dsimp only
  rw [←source_original_root_FUNCTIONAL_ROOT_EXACT434,
    ←source_original_root_FUNCTIONAL_ROOT_SUM434]
  apply source_original_root_FUNCTIONAL_ROOT_CONGR_LENGTH434
    SP sm BP bm J ell m cap patterns
  intro H hH
  apply source_original_root_LIST_FOREST_EXPANSION434
  rw [hH]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFunctionalScale -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)



theorem source_original_root_PADDED_G_SCALE434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (c : ℂ) (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => c*F Y H') X =
    c*sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F X := by
  simp_rw [source_original_root_PADDED_G_FLAT434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem source_original_root_PADDED_E_SCALE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (c : ℂ) (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (fun Y H' => c*F Y H') X =
    c*sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H F X := by
  simp_rw [source_original_root_PADDED_E_FLAT434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem source_original_root_FUNCTIONAL_SCALE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (c : ℂ) (F : Output → List (Option ℕ) → ℂ)
    (n start : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (fun out H' => c*F out H') n start Y H =
    c*sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F n start Y H := by
  induction n generalizing start Y H with
  | zero =>
    exact source_original_root_PADDED_G_SCALE434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H c F Y
  | succ n ih =>
    have hm (P : Prop) [Decidable P] (z : ℂ) :
        (if P then c*z else 0)=c*(if P then z else 0) := by
      by_cases hp : P <;> simp [hp]
    simp only [sourceOriginalRootFunctionalChain434,ih]
    simp_rw [hm]
    simp_rw [source_original_root_PADDED_E_SCALE434,hm]
    exact source_original_root_PADDED_G_SCALE434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H c _ Y

theorem source_original_root_FUNCTIONAL_ROOT_SCALE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (c : ℂ) (test : List (Option ℕ) → ℂ) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (fun H => c*test H) =
    c*sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T test := by
  unfold sourceOriginalRootFunctionalRoot434
  dsimp only
  simp_rw [mul_assoc,source_original_root_FUNCTIONAL_SCALE434]
  have hm (P : Prop) [Decidable P] (z : ℂ) :
      (if P then c*z else 0)=c*(if P then z else 0) := by
    by_cases hp : P <;> simp [hp]
  simp_rw [hm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootConstraintChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)




/-- Online child-batch equality constraints in the LITERAL source rows.
The original representatives, local ND, both OLD gates and final G are retained. -/
def sourceOriginalRootConstraintChain434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (terminal : Output → List (Option ℕ) → ℂ) :
    ℕ → ℕ → Output → List (Option ℕ) → ℂ
  | 0,i,Y,H =>
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun out H' => sourceOriginalRootForestBatch434 p H.length H'*terminal out H') Y
  | n+1,i,Y,H =>
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun yg hg => sourceOriginalRootForestBatch434 p H.length hg*
        (if (∑ g : BG,(yg.2 g).2.card)≤T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
            zeta theta (physicalAlternatingSign i) k hg
            (fun out ht => sourceOriginalRootForestBatch434 p hg.length ht*
              (if (∑ g : BG,(out.2 g).2.card)≤T then
                sourceOriginalRootConstraintChain434 p q rho Vs V mu K zeta theta k N T terminal
                  n (i+1) out ht else 0)) yg else 0)) Y

theorem source_original_root_PADDED_G_PREFIX434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => sourceOriginalRootForestPrefix434 p H'*F Y H') X =
    sourceOriginalRootForestPrefix434 p H*
      sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
        (fun Y H' => sourceOriginalRootForestBatch434 p H.length H'*F Y H') X := by
  simp_rw [source_original_root_PADDED_G_FLAT434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [source_original_root_FOREST_PREFIX_WRITE434]
  ring

theorem source_original_root_PADDED_E_PREFIX434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (fun Y H' => sourceOriginalRootForestPrefix434 p H'*F Y H') X =
    sourceOriginalRootForestPrefix434 p H*
      sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
        zeta theta o k H (fun Y H' => sourceOriginalRootForestBatch434 p H.length H'*F Y H') X := by
  simp_rw [source_original_root_PADDED_E_FLAT434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [source_original_root_FOREST_PREFIX_WRITE434]
  ring

/-- Actual terminal-to-online factorization, including every intermediate
orbit conditional mean. No saving, injectivity, or changed history law is assumed. -/
theorem source_original_root_ACTUAL_CONSTRAINT_FACTOR434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (terminal : Output → List (Option ℕ) → ℂ)
    (n i : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T
      (fun out H' => sourceOriginalRootForestPrefix434 p H'*terminal out H') n i Y H =
    sourceOriginalRootForestPrefix434 p H*
      sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns
        p q rho Vs V mu K zeta theta k N T terminal n i Y H := by
  induction n generalizing i Y H with
  | zero =>
    exact source_original_root_PADDED_G_PREFIX434 SP sm BP bm J ell cap
      p q rho N i T Vs V mu H terminal Y
  | succ n ih =>
    have hm (P : Prop) [Decidable P] (a b : ℂ) :
        (if P then a*b else 0)=a*(if P then b else 0) := by
      by_cases hp : P <;> simp [hp]
    simp only [sourceOriginalRootFunctionalChain434,sourceOriginalRootConstraintChain434,ih]
    simp_rw [hm,source_original_root_PADDED_E_PREFIX434,hm]
    exact source_original_root_PADDED_G_PREFIX434 SP sm BP bm J ell cap
      p q rho N i T Vs V mu H _ Y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootCoherentConstraint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 700000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Exact original coherent forest functional as the initial physical
sum of the literal constrained suffix. No new boundary law is introduced. -/
theorem source_original_root_COHERENT_CONSTRAINT_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T)) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T
      (fun H => sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H)) =
    (physicalSourceBaselineProduct BP bm q (2*R):ℂ)*
      ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        (physicalOrbitMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) y:ℂ)*
        star (physicalVacuum SP sm BP bm J ell y)*
        (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
          sourceOriginalRootForestPrefix434 p
            ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)*
          sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns p
            q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
            K zeta theta k (2*R) T
            (fun out _ => physicalVacuum SP sm BP bm J ell out) (2*R) 0 y
            ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)
         else 0) := by
  unfold sourceOriginalRootFunctionalRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · rw [if_pos hn,if_pos hn]
    congr 1
    calc
      _ = sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T
          (fun out H => sourceOriginalRootForestPrefix434 p H*physicalVacuum SP sm BP bm J ell out)
          (2*R) 0 y ((physicalOutputInitialBirths SP sm BP bm J ell y).map some) := by
        apply source_original_root_FUNCTIONAL_CONGR_LENGTH434 SP sm BP bm J ell m cap patterns
        intro out H hH
        have hlen : A ≤ H.length := by
          rw [source_original_root_INITIAL_PAD_LENGTH434] at hH
          rw [hH,hA]
          apply le_of_eq
          ring
        rw [source_original_root_FOREST_PREFIX_FULL434 p H hlen]
      _ = _ := source_original_root_ACTUAL_CONSTRAINT_FACTOR434
        SP sm BP bm J ell m cap patterns p q rho Vs V
        (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) T
        (fun out _ => physicalVacuum SP sm BP bm J ell out) (2*R) 0 y
        ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)
  · rw [if_neg hn,if_neg hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootBoundary -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Integrate the actual constrained suffix over the original initial law.
This intermediate adapter pays the full vacuum energy exactly once. -/
theorem source_original_global_root_CONSTRAINT_BOUNDARY434
    (q rho : ℝ) (R T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (B w : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : Output,
      (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup →
      ‖sourceOriginalRootForestPrefix434 p
          ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)*
        sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns p
          q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T
          (fun out _ => physicalVacuum SP sm BP bm J ell out) (2*R) 0 y
          ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)‖ ≤
      B*w^(∑ g,(y.2 g).2.card)) :
    ‖sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListForestTerm434 p)‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V) (physicalVacuum SP sm BP bm J ell) * B := by
  have hs : sourceOriginalRootListForestTerm434 p =
      (fun H => (-1:ℂ)^sourceOriginalRootForestRank434 p *
        sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H)) := rfl
  rw [hs,source_original_root_FUNCTIONAL_ROOT_SCALE434,norm_mul]
  simp only [norm_pow,norm_neg,norm_one,one_pow,one_mul]
  rw [source_original_root_COHERENT_CONSTRAINT_EXACT434 SP sm BP bm J ell m cap patterns
    q rho Vs V K zeta theta k R T p hA,norm_mul]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) y:ℂ)*
          star (physicalVacuum SP sm BP bm J ell y)*
          (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
            sourceOriginalRootForestPrefix434 p
              ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)*
            sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns p
              q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
              K zeta theta k (2*R) T
              (fun out _ => physicalVacuum SP sm BP bm J ell out) (2*R) 0 y
              ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)
           else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        (physicalOrbitMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) y *
          ‖physicalVacuum SP sm BP bm J ell y‖^2)*B := by
      apply Finset.sum_le_sum
      intro y hy
      have hm := (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs
        (physicalSourceMuTilde BP bm q (2*R) V) hVs hmu y hy).le
      by_cases hv : ∀ g : BG,(y.2 g).2=0
      · have ho : (∑ g,(y.2 g).2.card)=0 := by simp only [hv,Multiset.card_zero,Finset.sum_const_zero]
        have hvac : physicalVacuum SP sm BP bm J ell y=1 := by simp [physicalVacuum,hv]
        rw [hvac]
        simp only [star_one,mul_one,norm_one,one_pow,mul_one]
        by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        · rw [if_pos hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
          have hb := hbound y hn
          rw [ho,pow_zero,mul_one] at hb
          exact mul_le_mul_of_nonneg_left hb hm
        · rw [if_neg hn,mul_zero,norm_zero]
          exact mul_nonneg hm hB
      · have hvac : physicalVacuum SP sm BP bm J ell y=0 := by simp [physicalVacuum,hv]
        simp only [hvac,star_zero,mul_zero,zero_mul,norm_zero,zero_pow (by decide : 2≠0)]
        exact le_rfl
    _ = _ := by unfold sourceOriginalUnfilteredIdealOrbitEnergy434; rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestSuffix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 500000


def sourceOriginalRootBatchBudget434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T : ℕ) (delta gamma a : ℝ) :
    ℕ → ℕ → ℝ
  | 0,o => delta^(∑ g,(sourceOriginalRootForestQG434 p G T o g).card)*gamma
  | n+1,o =>
    (sourceOriginalRootBatchBudget434 p G M T delta gamma a n (o+Fintype.card G*T+Fintype.card G*M)*
      (delta^(∑ g,(sourceOriginalRootForestQE434 p G M (o+Fintype.card G*T) g).card)*a))*
      (delta^(∑ g,(sourceOriginalRootForestQG434 p G T o g).card)*gamma)

theorem source_original_root_BATCH_BUDGET_NONNEG434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T : ℕ) (delta gamma a : ℝ)
    (hd : 0 ≤ delta) (hg : 0 ≤ gamma) (ha : 0 ≤ a) (n o : ℕ) :
    0 ≤ sourceOriginalRootBatchBudget434 p G M T delta gamma a n o := by
  induction n generalizing o with
  | zero => exact mul_nonneg (pow_nonneg hd _) hg
  | succ n ih =>
    exact mul_nonneg (mul_nonneg (ih _) (mul_nonneg (pow_nonneg hd _) ha))
      (mul_nonneg (pow_nonneg hd _) hg)


def sourceOriginalRootBatchRank434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T : ℕ) : ℕ → ℕ → ℕ
  | 0,o => ∑ g,(sourceOriginalRootForestQG434 p G T o g).card
  | n+1,o => sourceOriginalRootBatchRank434 p G M T n (o+Fintype.card G*T+Fintype.card G*M)+
      (∑ g,(sourceOriginalRootForestQE434 p G M (o+Fintype.card G*T) g).card)+
      (∑ g,(sourceOriginalRootForestQG434 p G T o g).card)

theorem source_original_root_BATCH_BUDGET_CLOSED434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T : ℕ) (delta gamma a : ℝ) (n o : ℕ) :
    sourceOriginalRootBatchBudget434 p G M T delta gamma a n o=
      delta^(sourceOriginalRootBatchRank434 p G M T n o)*gamma^(n+1)*a^n := by
  induction n generalizing o with
  | zero => simp [sourceOriginalRootBatchBudget434,sourceOriginalRootBatchRank434]
  | succ n ih =>
    simp only [sourceOriginalRootBatchBudget434,sourceOriginalRootBatchRank434,ih,pow_add,pow_succ]
    ring

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


/-- High-rank suffix for the LITERAL constrained source chain, uniform in
every physical input and every correctly sized prior register. The pins
are derived from the actual forest, including same-batch and inactive
annihilation. The sole E premise is the accepted ordered pinned-row bound. -/
theorem source_original_root_ACTUAL_FOREST_SUFFIX434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho W w delta a : ℝ) (N T : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hd : 0 ≤ delta) (ha : 0 ≤ a)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤ delta*(∑ p : BP g,mu g p))
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (hrow : ∀ i Q pin x,
      sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
        Q pin w q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
        zeta theta (physicalAlternatingSign i) k x ≤
      (delta^(∑ g,(Q g).card)*a)*w^(∑ g,(x.2 g).2.1.val))
    (terminal : Output → List (Option ℕ) → ℂ)
    (hterminal : ∀ Y H,‖terminal Y H‖ ≤ w^(∑ g,(Y.2 g).2.card))
    (n i : ℕ) (Y : Output) (H : List (Option ℕ))
    (hA : H.length+(n+1)*(Fintype.card BG*T)+n*(Fintype.card BG*(J+ell)) ≤ A) :
    ‖sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns
      p q rho Vs V mu K zeta theta k N T terminal n i Y H‖ ≤
    sourceOriginalRootBatchBudget434 p BG (J+ell) T delta
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)) a n H.length*w^(∑ g,(Y.2 g).2.card) := by
  induction n generalizing i Y H with
  | zero =>
    have hA' : H.length+Fintype.card BG*T ≤ A := by simpa using hA
    have hh := source_original_root_G_BATCH_ROW_BOUND434 SP sm BP bm J ell cap
      p T H hA' q rho W w 1 delta N i hq hq1 hr hW hw (by norm_num) hd hcontrol
      Vs V mu hVs hV hVW hmu hmass hAtom (fun _ => True) terminal
      (fun Y H' _ => by simpa only [one_mul] using hterminal Y H') Y
    simpa only [sourceOriginalRootConstraintChain434,sourceOriginalRootBatchBudget434,ite_true,one_mul]
      using hh
  | succ n ih =>
    let C := sourceOriginalRootBatchBudget434 p BG (J+ell) T delta
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)) a n
      (H.length+Fintype.card BG*T+Fintype.card BG*(J+ell))
    let B := delta^(∑ g,(sourceOriginalRootForestQE434 p BG (J+ell)
      (H.length+Fintype.card BG*T) g).card)*a
    have hC : 0 ≤ C := source_original_root_BATCH_BUDGET_NONNEG434 p BG (J+ell) T delta
      _ a hd (Real.exp_pos _).le ha _ _
    have hB : 0 ≤ B := mul_nonneg (pow_nonneg hd _) ha
    have hAG : H.length+Fintype.card BG*T ≤ A := by
      simp only [Nat.add_mul,Nat.one_mul] at hA
      omega
    simp only [sourceOriginalRootConstraintChain434]
    apply (source_original_root_G_BATCH_ROW_BOUND434 SP sm BP bm J ell cap
      p T H hAG q rho W w (C*B) delta N i hq hq1 hr hW hw
      (mul_nonneg hC hB) hd hcontrol Vs V mu hVs hV hVW hmu hmass hAtom
      (fun out => (∑ g,(out.2 g).2.card) ≤ T) _ _ Y).trans_eq
    · rfl
    · intro YG HG hHG
      have hAE : HG.length+Fintype.card BG*(J+ell) ≤ A := by
        rw [hHG]
        simp only [Nat.add_mul,Nat.one_mul] at hA
        omega
      have hERow (x : State) :
          sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
            (sourceOriginalRootForestQE434 p BG (J+ell) HG.length)
            (sourceOriginalRootForestPinE434 p BG (J+ell) HG.length HG)
            w q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
            zeta theta (physicalAlternatingSign i) k x ≤ B*w^(∑ g,(x.2 g).2.1.val) := by
        calc
          _ ≤ (delta^(∑ g,(sourceOriginalRootForestQE434 p BG (J+ell) HG.length g).card)*a)*
              w^(∑ g,(x.2 g).2.1.val) :=
            hrow i (sourceOriginalRootForestQE434 p BG (J+ell) HG.length)
              (sourceOriginalRootForestPinE434 p BG (J+ell) HG.length HG) x
          _ = _ := by dsimp only [B]; rw [hHG]
      apply source_original_root_E_BATCH_ROW_BOUND434 SP sm BP bm J ell m cap patterns
        p HG hAE w C B q rho hw.le hC hB Vs V mu hVs hmu
        (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
        zeta theta (physicalAlternatingSign i) k hERow
      intro YE HE hHE
      have hAE' : HE.length+(n+1)*(Fintype.card BG*T)+n*(Fintype.card BG*(J+ell)) ≤ A := by
        rw [hHE,hHG]
        simp only [Nat.add_mul,Nat.one_mul] at hA ⊢
        omega
      have hh := ih (i+1) YE HE hAE'
      simpa only [hHE,hHG] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFunctionalValid -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_root_PADDED_G_CONGR_VALID434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ)) (hH : sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H)
    (F F' : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*T →
      sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H' → F Y H'=F' Y H')
    (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F X =
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F' X := by
  unfold sourceOriginalRootPaddedG434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  rw [hF _ _ (by simp only [List.length_append,source_original_root_G_PAD_LENGTH434])
    (source_original_root_VALID_APPEND434 _ _ _ hH
      (source_original_root_G_PAD_VALID434 SP sm BP bm J ell cap T _ _))]

theorem source_original_root_PADDED_E_CONGR_VALID434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ)) (hH : sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H)
    (F F' : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*(J+ell) →
      sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H' → F Y H'=F' Y H')
    (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H F X =
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H F' X := by
  unfold sourceOriginalRootPaddedE434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro z hz
  rw [hF _ _ (by simp only [List.length_append,source_original_root_E_PAD_LENGTH434])
    (source_original_root_VALID_APPEND434 _ _ _ hH
      (source_original_root_E_PAD_VALID434 SP sm BP bm J ell m cap patterns _ _))]

/-- Final-register replacement only at the fixed potential length.
This includes the terminal G batch, even though its performed births vanish. -/
theorem source_original_root_FUNCTIONAL_CONGR_VALID434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (n start : ℕ) (F F' : Output → List (Option ℕ) → ℂ)
    (Y : Output) (H : List (Option ℕ))
    (hH : sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H)
    (hF : ∀ Y' H',H'.length=H.length+(n+1)*(Fintype.card BG*T)+n*(Fintype.card BG*(J+ell)) →
      sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H' → F Y' H'=F' Y' H') :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F n start Y H =
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F' n start Y H := by
  induction n generalizing start Y H with
  | zero =>
    apply source_original_root_PADDED_G_CONGR_VALID434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H hH F F'
    intro Y' H' hh hv
    exact hF Y' H' (by simpa using hh) hv
  | succ n ih =>
    simp only [sourceOriginalRootFunctionalChain434]
    apply source_original_root_PADDED_G_CONGR_VALID434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H hH
    intro yg hg hhg hvg
    by_cases hold : (∑ g : BG,(yg.2 g).2.card)≤T
    · rw [if_pos hold,if_pos hold]
      apply source_original_root_PADDED_E_CONGR_VALID434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
        zeta theta (physicalAlternatingSign start) k hg hvg
      intro out ht hht hvt
      by_cases hold' : (∑ g : BG,(out.2 g).2.card)≤T
      · rw [if_pos hold',if_pos hold']
        apply ih _ _ _ hvt
        intro Y' H' hh hv
        apply hF _ _ _ hv
        rw [hht,hhg] at hh
        simp only [Nat.add_mul,Nat.one_mul] at *
        omega
      · rw [if_neg hold',if_neg hold']
    · rw [if_neg hold,if_neg hold]

theorem source_original_root_FUNCTIONAL_ROOT_CONGR_VALID434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (test test' : List (Option ℕ) → ℂ)
    (heq : ∀ H,H.length=Fintype.card BG*(J+ell)+(2*R+1)*(Fintype.card BG*T)+
      (2*R)*(Fintype.card BG*(J+ell)) →
      sourceOriginalRootValid434 (sourceOriginalRootActualAlphabet434 BP bm) H → test H=test' H) :
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T test =
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T test' := by
  unfold sourceOriginalRootFunctionalRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell Y).Nodup
  · rw [if_pos hn,if_pos hn]
    congr 1
    apply source_original_root_FUNCTIONAL_CONGR_VALID434
      SP sm BP bm J ell m cap patterns
      (hH := source_original_root_INITIAL_VALID434 SP sm BP bm J ell Y)
    intro Y' H' hH' hv
    rw [source_original_root_INITIAL_PAD_LENGTH434] at hH'
    rw [heq H' hH' hv]
  · rw [if_neg hn,if_neg hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootEdgeAverage -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)



/-- The literal source root of ANY fixed finite edge-equality product is
an exact independent-field average of the literal phased source root.
Random centering scalars stay inside the average. -/
theorem source_original_root_FUNCTIONAL_EDGE_AVERAGE434
    {E : Type} [Fintype E]
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T A : ℕ)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (left right : E → Fin A) :
    let S := sourceOriginalRootActualAlphabet434 BP bm
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T
      (fun H => ∏ e : E,if sourceOriginalRootListLabel434 H (left e).val =
        sourceOriginalRootListLabel434 H (right e).val then (1:ℂ) else 0) =
    ∑ h : E → (S ⊕ Fin A) → Bool,
      ((∏ e : E,sourceOriginalRootSign434 (h e (Sum.inr (left e))) *
          sourceOriginalRootSign434 (h e (Sum.inr (right e)))) /
        (Fintype.card (E → (S ⊕ Fin A) → Bool):ℂ)) *
      sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T
        (sourceOriginalRootListPhase434 (sourceOriginalRootNumericSlotPhase434 S left right h) 0) := by
  dsimp only
  simp_rw [←source_original_root_FUNCTIONAL_ROOT_SCALE434]
  rw [←source_original_root_FUNCTIONAL_ROOT_SUM434]
  apply source_original_root_FUNCTIONAL_ROOT_CONGR_VALID434
    SP sm BP bm J ell m cap patterns
  intro H hH hv
  have hlen : H.length=A := by rw [hH,hA]; ring
  have hh := source_original_root_NUMERIC_EDGE_AVERAGE434
    (sourceOriginalRootActualAlphabet434 BP bm) left right H hlen
    (fun a p hp => source_original_root_VALID_GET434 _ H hv a.val p
      (by rw [hlen]; exact a.isLt) hp)
  rw [←hh,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- Coherent pairing version of the actual source edge average. The
initial ket includes the initial ND mask and conjugated phase; the
terminal state is the WHOLE original vacuum. -/
theorem source_original_root_FUNCTIONAL_EDGE_PAIR_AVERAGE434
    {E : Type} [Fintype E]
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T A : ℕ)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (left right : E → Fin A) :
    let S := sourceOriginalRootActualAlphabet434 BP bm
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T
      (fun H => ∏ e : E,if sourceOriginalRootListLabel434 H (left e).val =
        sourceOriginalRootListLabel434 H (right e).val then (1:ℂ) else 0) =
    ∑ h : E → (S ⊕ Fin A) → Bool,
      ((∏ e : E,sourceOriginalRootSign434 (h e (Sum.inr (left e))) *
          sourceOriginalRootSign434 (h e (Sum.inr (right e)))) /
        (Fintype.card (E → (S ⊕ Fin A) → Bool):ℂ)) *
      ((physicalSourceBaselineProduct BP bm q (2*R):ℂ) *
        physicalSymmetricInner SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V)
          (sourceOriginalRootInitialKet434 SP sm BP bm J ell
            (sourceOriginalRootNumericSlotPhase434 S left right h))
          (sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
            K zeta theta k (2*R) T (sourceOriginalRootNumericSlotPhase434 S left right h)
            (physicalVacuum SP sm BP bm J ell) (2*R) 0 (Fintype.card BG*(J+ell)))) := by
  rw [source_original_root_FUNCTIONAL_EDGE_AVERAGE434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T A hA left right]
  simp_rw [source_original_root_FUNCTIONAL_PHASE_PAIR434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestAverage -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- Unselected children are loops. Their independent fields cancel
identically; selected children retain their strictly earlier parent. -/
def sourceOriginalRootForestParent434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (i : Fin A) : Fin A :=
  (p i).elim i (fun j => ⟨j.val,lt_trans j.isLt i.isLt⟩)

theorem source_original_root_FOREST_EQUALITY_EDGES434
    {A : ℕ} {B : Type} (p : SourceOriginalRootForest434 A) (x : ℕ → B) :
    sourceOriginalRootForestEquality434 p x =
      ∏ i : Fin A,if x i.val=x (sourceOriginalRootForestParent434 p i).val then (1:ℂ) else 0 := by
  unfold sourceOriginalRootForestEquality434
  apply Finset.prod_congr rfl
  intro i hi
  cases hp : p i <;> simp [sourceOriginalRootForestParent434,hp]

def sourceOriginalRootForestSlotPhase434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) : ℕ → Option ℕ → ℂ :=
  sourceOriginalRootNumericSlotPhase434 S id (sourceOriginalRootForestParent434 p) h

theorem source_original_root_FOREST_SLOT_UNIT434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) (i : ℕ) (v : Option ℕ) :
    ‖sourceOriginalRootForestSlotPhase434 S p h i v‖=1 :=
  source_original_root_NUMERIC_SLOT_UNIT434 S id (sourceOriginalRootForestParent434 p) h i v

theorem source_original_root_FOREST_SLOT_INACTIVE434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) (i : ℕ) :
    sourceOriginalRootForestSlotPhase434 S p h i none=1 :=
  source_original_root_NUMERIC_SLOT_INACTIVE434 S id (sourceOriginalRootForestParent434 p) h i

def sourceOriginalRootForestCenter434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) : ℂ :=
  ∏ i : Fin A,sourceOriginalRootSign434 (h i (Sum.inr i)) *
    sourceOriginalRootSign434 (h i (Sum.inr (sourceOriginalRootForestParent434 p i)))

theorem source_original_root_FOREST_CENTER_UNIT434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) :
    ‖sourceOriginalRootForestCenter434 S p h‖=1 := by
  simp [sourceOriginalRootForestCenter434,norm_prod,norm_mul,source_original_root_SIGN_NORM434]


/-- Scalar specialization factored through an abstract linear functional;
the actual source instantiation below supplies both identities. -/
theorem source_original_root_LINEAR_FOREST_AVERAGE434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (ev : (List (Option ℕ) → ℂ) → ℂ)
    (hscale : ∀ c f,ev (fun H => c*f H)=c*ev f)
    (haverage : ev (fun H => ∏ i : Fin A,if sourceOriginalRootListLabel434 H (id i).val =
        sourceOriginalRootListLabel434 H (sourceOriginalRootForestParent434 p i).val then (1:ℂ) else 0) =
      ∑ h : Fin A → (S ⊕ Fin A) → Bool,
        ((∏ i : Fin A,sourceOriginalRootSign434 (h i (Sum.inr (id i))) *
          sourceOriginalRootSign434 (h i (Sum.inr (sourceOriginalRootForestParent434 p i)))) /
          (Fintype.card (Fin A → (S ⊕ Fin A) → Bool):ℂ)) *
        ev (sourceOriginalRootListPhase434
          (sourceOriginalRootNumericSlotPhase434 S id (sourceOriginalRootForestParent434 p) h) 0)) :
    ev (sourceOriginalRootListForestTerm434 p) =
      (-1:ℂ)^sourceOriginalRootForestRank434 p *
      ∑ h : Fin A → (S ⊕ Fin A) → Bool,
        (sourceOriginalRootForestCenter434 S p h /
          (Fintype.card (Fin A → (S ⊕ Fin A) → Bool):ℂ)) *
        ev (sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h) 0) := by
  have ht : sourceOriginalRootListForestTerm434 p =
      (fun H => (-1:ℂ)^sourceOriginalRootForestRank434 p *
        ∏ i : Fin A,if sourceOriginalRootListLabel434 H i.val =
          sourceOriginalRootListLabel434 H (sourceOriginalRootForestParent434 p i).val
          then (1:ℂ) else 0) := by
    funext H
    unfold sourceOriginalRootListForestTerm434
    apply congrArg (fun z : ℂ => (-1:ℂ)^sourceOriginalRootForestRank434 p*z)
    unfold sourceOriginalRootForestEquality434
    apply Finset.prod_congr rfl
    intro i hi
    cases hp : p i with
    | none => simp [sourceOriginalRootForestParent434,hp]
    | some j =>
      simp only [hp,Option.elim,sourceOriginalRootForestParent434]
      exact congrArg (fun d : Decidable (sourceOriginalRootListLabel434 H i.val =
          sourceOriginalRootListLabel434 H j.val) => @ite ℂ _ d 1 0) (Subsingleton.elim _ _)
  rw [ht,hscale]
  apply congrArg (fun z : ℂ => (-1:ℂ)^sourceOriginalRootForestRank434 p*z)
  simpa only [sourceOriginalRootForestCenter434,sourceOriginalRootForestSlotPhase434,id_eq] using haverage


theorem source_original_root_FOREST_SCALAR_AVERAGE434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H : List (Option ℕ)) (hH : H.length=A)
    (hv : ∀ a : Fin A,∀ v,H.getD a.val none=some v → v∈S) :
    sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H) =
      ∑ h : Fin A → (S ⊕ Fin A) → Bool,
        (sourceOriginalRootForestCenter434 S p h /
          (Fintype.card (Fin A → (S ⊕ Fin A) → Bool):ℂ)) *
        sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h) 0 H := by
  have hh := source_original_root_NUMERIC_EDGE_AVERAGE434 S id
    (sourceOriginalRootForestParent434 p) H hH hv
  have he :
      sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H) =
      ∏ i : Fin A,if sourceOriginalRootListLabel434 H (id i).val =
        sourceOriginalRootListLabel434 H (sourceOriginalRootForestParent434 p i).val
        then (1:ℂ) else 0 := by
    unfold sourceOriginalRootForestEquality434
    apply Finset.prod_congr rfl
    intro i hi
    cases hp : p i with
    | none => simp [sourceOriginalRootForestParent434,hp]
    | some j =>
      simp only [hp,Option.elim,sourceOriginalRootForestParent434,id_eq]
      exact congrArg (fun d : Decidable (sourceOriginalRootListLabel434 H i.val =
        sourceOriginalRootListLabel434 H j.val) => @ite ℂ _ d 1 0) (Subsingleton.elim _ _)
  rw [he,←hh,Finset.sum_div]
  simp only [Fintype.card_eq_nat_card]
  apply Finset.sum_congr (by ext h; simp)
  intro h hh
  unfold sourceOriginalRootForestCenter434 sourceOriginalRootForestSlotPhase434
  rw [div_mul_eq_mul_div]
  congr 2

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exact original source forest term as a signed centered average of
actual source slot phases, with no injectivity or averaging hypothesis. -/
theorem source_original_root_FOREST_TERM_AVERAGE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T A : ℕ)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (p : SourceOriginalRootForest434 A) :
    let S := sourceOriginalRootActualAlphabet434 BP bm
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListForestTerm434 p) =
    (-1:ℂ)^sourceOriginalRootForestRank434 p *
      ∑ h : Fin A → (S ⊕ Fin A) → Bool,
        (sourceOriginalRootForestCenter434 S p h /
          (Fintype.card (Fin A → (S ⊕ Fin A) → Bool):ℂ)) *
        sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
          q rho Vs V K zeta theta k R T
          (sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h) 0) := by
  dsimp only
  unfold sourceOriginalRootListForestTerm434
  rw [source_original_root_FUNCTIONAL_ROOT_SCALE434]
  apply congrArg (fun z : ℂ => (-1:ℂ)^sourceOriginalRootForestRank434 p*z)
  simp_rw [←source_original_root_FUNCTIONAL_ROOT_SCALE434]
  rw [←source_original_root_FUNCTIONAL_ROOT_SUM434]
  apply source_original_root_FUNCTIONAL_ROOT_CONGR_VALID434
    SP sm BP bm J ell m cap patterns
  intro H hH hv
  have hlen : H.length=A := by rw [hH,hA]; ring
  exact source_original_root_FOREST_SCALAR_AVERAGE434
    (sourceOriginalRootActualAlphabet434 BP bm) p H hlen
    (fun a v hp => source_original_root_VALID_GET434 _ H hv a.val v
      (by rw [hlen]; exact a.isLt) hp)

/-- Exact finite Rademacher expansion of the EXISTING ORIGINAL root.
Every phase is inside its actual source row and every centering scalar
remains inside its finite expectation. -/
theorem source_original_root_ORIGINAL_FOREST_PHASE_SUM434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    let A := (2*R+1)*Fintype.card BG*(J+ell+T)
    let S := sourceOriginalRootActualAlphabet434 BP bm
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    ∑ p : SourceOriginalRootForest434 A,
      (-1:ℂ)^sourceOriginalRootForestRank434 p *
        ∑ h : Fin A → (S ⊕ Fin A) → Bool,
          (sourceOriginalRootForestCenter434 S p h /
            (Fintype.card (Fin A → (S ⊕ Fin A) → Bool):ℂ)) *
          sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
            q rho Vs V K zeta theta k R T
            (sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h) 0) := by
  rw [source_original_root_ORIGINAL_FOREST_SUM434]
  apply Finset.sum_congr rfl
  intro p hp
  exact source_original_root_FOREST_TERM_AVERAGE434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T _ rfl p
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootAverageBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A normalized finite independent-field average has variation one.
There is no alphabet-size or number-of-fields loss. -/
theorem source_original_root_UNIT_AVERAGE_BOUND434
    {O : Type} [Fintype O] [Nonempty O] (c f : O → ℂ)
    (hc : ∀ o,‖c o‖=1) (B : ℝ) (hf : ∀ o,‖f o‖ ≤ B) :
    ‖∑ o : O,(c o/(Fintype.card O:ℂ))*f o‖ ≤ B := by
  have hcard : (0:ℝ)<Fintype.card O := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ ∑ o : O,‖(c o/(Fintype.card O:ℂ))*f o‖ := norm_sum_le _ _
    _ ≤ ∑ o : O,(1/(Fintype.card O:ℝ))*B := by
      apply Finset.sum_le_sum
      intro o ho
      simp only [norm_mul,norm_div,hc o,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hf o) (by positivity)
    _ = B := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestOwners -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

def sourceOriginalRootSelected434 {A : ℕ} (p : SourceOriginalRootForest434 A) : Finset (Fin A) :=
  Finset.univ.filter (fun i => (p i).isSome)

def sourceOriginalRootMarkedOwners434 {Owner : Type} [DecidableEq Owner]
    {A : ℕ} (owner : ℕ → Owner) (p : SourceOriginalRootForest434 A) : Finset Owner :=
  (sourceOriginalRootSelected434 p).image (fun i => owner i.val) ∪
  (sourceOriginalRootSelected434 p).image (fun i => owner (sourceOriginalRootForestParent434 p i).val)

theorem source_original_root_FOREST_OWNER_COUNT434
    {Owner : Type} [DecidableEq Owner] {A : ℕ}
    (owner : ℕ → Owner) (p : SourceOriginalRootForest434 A) :
    (sourceOriginalRootMarkedOwners434 owner p).card ≤ 2*sourceOriginalRootForestRank434 p := by
  have h1 := Finset.card_image_le (s := sourceOriginalRootSelected434 p) (f := fun i => owner i.val)
  have h2 := Finset.card_image_le (s := sourceOriginalRootSelected434 p)
    (f := fun i => owner (sourceOriginalRootForestParent434 p i).val)
  have hr : (sourceOriginalRootSelected434 p).card=sourceOriginalRootForestRank434 p :=
    (source_original_root_FOREST_RANK_CARD434 p).symm
  have hh := Finset.card_union_le
    ((sourceOriginalRootSelected434 p).image (fun i => owner i.val))
    ((sourceOriginalRootSelected434 p).image (fun i => owner (sourceOriginalRootForestParent434 p i).val))
  change _ ≤ _ at hh
  unfold sourceOriginalRootMarkedOwners434
  omega

theorem source_original_root_SIGN_PAIR_SQUARE434 (b c : Bool) :
    (sourceOriginalRootSign434 b*sourceOriginalRootSign434 c)*
      (sourceOriginalRootSign434 b*sourceOriginalRootSign434 c)=1 := by
  calc
    _ = (sourceOriginalRootSign434 b*sourceOriginalRootSign434 b)*
        (sourceOriginalRootSign434 c*sourceOriginalRootSign434 c) := by ring
    _ = 1 := by rw [source_original_root_SIGN_SQUARE434,source_original_root_SIGN_SQUARE434]; norm_num

/-- Unselected-loop fields cancel pointwise. Only selected endpoints
can mark an owner; counting ALL random fields would give a wrong rank cost. -/
theorem source_original_root_FOREST_SLOT_UNMARKED434
    {Owner : Type} [DecidableEq Owner] (S : Finset ℕ) {A : ℕ}
    (owner : ℕ → Owner) (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) (j : ℕ) (v : Option ℕ)
    (hjmark : owner j∉sourceOriginalRootMarkedOwners434 owner p) :
    sourceOriginalRootForestSlotPhase434 S p h j v=1 := by
  unfold sourceOriginalRootForestSlotPhase434 sourceOriginalRootNumericSlotPhase434
  by_cases hj : j<A
  · rw [dif_pos hj]
    unfold sourceOriginalRootCenteredSlot434
    apply Finset.prod_eq_one
    intro e he
    cases hp : p e with
    | none =>
      simp only [id_eq,sourceOriginalRootForestParent434,hp,Option.elim]
      by_cases heq : e=(⟨j,hj⟩:Fin A)
      · rw [if_pos heq]
        exact source_original_root_SIGN_PAIR_SQUARE434 _ _
      · rw [if_neg heq,one_mul]
    | some b =>
      have hs : e∈sourceOriginalRootSelected434 p := by
        simp [sourceOriginalRootSelected434,hp]
      have hl : e≠(⟨j,hj⟩:Fin A) := by
        intro heq
        apply hjmark
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨e,hs,by rw [heq]⟩
      have hr : sourceOriginalRootForestParent434 p e≠(⟨j,hj⟩:Fin A) := by
        intro heq
        apply hjmark
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨e,hs,by rw [heq]⟩
      simp only [id_eq,if_neg hl,if_neg hr,one_mul]
  · rw [dif_neg hj]

theorem source_original_root_LIST_PHASE_ONE_ON_RANGE434
    {B : Type} (phi : ℕ → B → ℂ) (H : List B) (o : ℕ)
    (hone : ∀ j,o≤j → j<o+H.length → ∀ b,phi j b=1) :
    sourceOriginalRootListPhase434 phi o H=1 := by
  induction H generalizing o with
  | nil => rfl
  | cons b H ih =>
    rw [sourceOriginalRootListPhase434,hone o (by omega) (by simp) b,one_mul]
    apply ih
    intro j hj hj' b'
    exact hone j (by omega) (by simp only [List.length_cons]; omega) b'

/-- Fixed arithmetic owner map. Initial and G addresses may overmark
owners, harmlessly; every E slot has exactly its visit's owner. -/
def sourceOriginalRootVisitOwner434 (initial gwidth ewidth j : ℕ) : ℕ :=
  (j-initial)/(gwidth+ewidth)

theorem source_original_root_E_SLOT_OWNER434
    (initial gwidth ewidth i t : ℕ) (ht : t<ewidth) :
    sourceOriginalRootVisitOwner434 initial gwidth ewidth
      (initial+i*(gwidth+ewidth)+gwidth+t)=i := by
  have hd : 0<gwidth+ewidth := by omega
  have ht' : gwidth+t<gwidth+ewidth := by omega
  have he : initial+i*(gwidth+ewidth)+gwidth+t =
      initial+((gwidth+t)+(gwidth+ewidth)*i) := by ring
  unfold sourceOriginalRootVisitOwner434
  rw [he,Nat.add_sub_cancel_left,Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt ht',Nat.zero_add]

theorem source_original_root_UNMARKED_E_LIST_PHASE434
    (S : Finset ℕ) {A : ℕ} (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool)
    (initial gwidth ewidth i : ℕ) (H : List (Option ℕ)) (hH : H.length=ewidth)
    (hi : i∉sourceOriginalRootMarkedOwners434
      (sourceOriginalRootVisitOwner434 initial gwidth ewidth) p) :
    sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h)
      (initial+i*(gwidth+ewidth)+gwidth) H=1 := by
  apply source_original_root_LIST_PHASE_ONE_ON_RANGE434
  intro j hj hj' v
  apply source_original_root_FOREST_SLOT_UNMARKED434 S
    (sourceOriginalRootVisitOwner434 initial gwidth ewidth) p h j v
  have ht : j-(initial+i*(gwidth+ewidth)+gwidth)<ewidth := by rw [hH] at hj'; omega
  have he : j=initial+i*(gwidth+ewidth)+gwidth+
      (j-(initial+i*(gwidth+ewidth)+gwidth)) := by omega
  rw [he,source_original_root_E_SLOT_OWNER434 _ _ _ _ _ ht]
  exact hi
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootHarmonicBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Elementary harmonic bound, uniform in arbitrary subsets of positive
integers. It does not assume the source SMALL harmonic normalization. -/
theorem source_original_root_HARMONIC_SUBSET434
    (s : Finset ℕ) (B : ℝ) (hB : 1≤B)
    (hp : ∀ p∈s,0<p) (hu : ∀ p∈s,(p:ℝ)≤B) :
    (∑ p∈s,1/(p:ℝ))≤1+Real.log B := by
  have hfloor : 1≤Nat.floor B := by
    simpa using Nat.floor_le_floor hB
  have hsub : s⊆Finset.Icc 1 (Nat.floor B) := by
    intro p hps
    refine Finset.mem_Icc.mpr ⟨hp p hps,?_⟩
    simpa using Nat.floor_le_floor (hu p hps)
  have hh : (∑ p∈Finset.Icc 1 (Nat.floor B),1/(p:ℝ))≤
      1+Real.log (Nat.floor B:ℝ) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log (Nat.floor B)
  calc
    _ ≤ ∑ p∈Finset.Icc 1 (Nat.floor B),1/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => by positivity)
    _ ≤ 1+Real.log (Nat.floor B:ℝ) := hh
    _ ≤ _ := by
      have hlog := Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor))
        (Nat.floor_le (zero_le_one.trans hB))
      linarith

theorem source_original_root_SMALL_HARMONIC_LINEAR434
    (s : Finset ℕ) (L b : ℝ) (hL : 1≤L) (hb : b≤1)
    (hp : ∀ p∈s,0<p) (hu : ∀ p∈s,(p:ℝ)≤Real.exp (L^b)) :
    (∑ p∈s,1/(p:ℝ))≤2*L := by
  have hLb : 0≤L^b := Real.rpow_nonneg (zero_le_one.trans hL) _
  have hh := source_original_root_HARMONIC_SUBSET434 s (Real.exp (L^b))
    (Real.one_le_exp_iff.mpr hLb) hp hu
  rw [Real.log_exp] at hh
  have hpow : L^b≤L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL hb
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPhaseEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalRootEnergyBudget434 (gamma : ℝ) (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,_ => gamma
  | n+1,i => gamma*a i*sourceOriginalRootEnergyBudget434 gamma a n (i+1)

theorem source_original_root_ENERGY_BUDGET_NONNEG434
    (gamma : ℝ) (a : ℕ → ℝ) (hg : 0 ≤ gamma) (ha : ∀ i,0 ≤ a i) (n i : ℕ) :
    0 ≤ sourceOriginalRootEnergyBudget434 gamma a n i := by
  induction n generalizing i with
  | zero => exact hg
  | succ n ih => exact mul_nonneg (mul_nonneg hg (ha i)) (ih _)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- FULL actual G for fixed potential slot phases, including b>T branches
and the terminal G. No truncation or rho-density transfer is used. -/
theorem source_original_root_SLOT_G_ENERGY434
    (q rho vmax : ℝ) (N i T offset : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho) (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phi : ℕ → Option ℕ → ℂ) (hphi : ∀ j v,‖phi j v‖=1) (F : Output → ℂ) :
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap q rho N i Vs V mu
        (fun x z => sourceOriginalRootListPhase434 phi offset
          (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  apply source_original_evolution_FINAL_SEEN_ERASED_G_ENERGY434
    SP sm BP bm J ell cap q rho vmax N i hq hq1 hquarter hr1 Vs hVs V hV hVW mu hmu hmass
  intro x z
  rw [source_original_root_LIST_PHASE_UNIT434 phi hphi]
  exact one_le_pow₀ (by norm_num)

/-- Exact fixed-offset composition of actual physical G and full phased
E. The E hypothesis is a local row-energy bank, discharged separately by
the original full contraction and arbitrary-phase polynomial theorems. -/
theorem source_original_root_PHASE_CHAIN_ENERGY434
    (q rho vmax : ℝ) (N T initial : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho) (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (phi : ℕ → Option ℕ → ℂ) (hphi : ∀ j v,‖phi j v‖=1) (a : ℕ → ℝ)
    (hE : ∀ i (F : Output → ℂ),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True)
          (fun x z => sourceOriginalRootListPhase434 phi
            (initial+i*(Fintype.card BG*T+Fintype.card BG*(J+ell))+Fintype.card BG*T)
            (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
          q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      (a i)^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F)
    (F : Output → ℂ) (n start : ℕ) :
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T phi F n start
        (initial+start*(Fintype.card BG*T+Fintype.card BG*(J+ell)))) ≤
    (sourceOriginalRootEnergyBudget434 gamma a n start)^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let W := max 1 vmax
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
  change _ ≤ (sourceOriginalRootEnergyBudget434 gamma a n start)^2*_
  induction n generalizing start with
  | zero =>
    exact source_original_root_SLOT_G_ENERGY434 SP sm BP bm J ell cap
      q rho vmax N start T _ hq hq1 hquarter hr1 Vs hVs V hV hVW mu hmu hmass phi hphi F
  | succ n ih =>
    let offset := initial+start*(Fintype.card BG*T+Fintype.card BG*(J+ell))
    have hoff : offset+Fintype.card BG*T+Fintype.card BG*(J+ell) =
        initial+(start+1)*(Fintype.card BG*T+Fintype.card BG*(J+ell)) := by dsimp [offset]; ring
    let H := sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T phi F n (start+1)
      (initial+(start+1)*(Fintype.card BG*T+Fintype.card BG*(J+ell)))
    let EF := sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True)
      (fun x z => sourceOriginalRootListPhase434 phi (offset+Fintype.card BG*T)
        (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
      q rho Vs V mu K T zeta theta (physicalAlternatingSign start) k H
    have hg := source_original_root_SLOT_G_ENERGY434 SP sm BP bm J ell cap
      q rho vmax N start T offset hq hq1 hquarter hr1 Vs hVs V hV hVW mu hmu hmass phi hphi EF
    have he := hE start H
    have hi := ih (start+1)
    simp only [sourceOriginalRootPhaseGEChain434]
    change sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap q rho N start Vs V mu
        (fun x z => sourceOriginalRootListPhase434 phi offset
          (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z))
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True)
          (fun x z => sourceOriginalRootListPhase434 phi (offset+Fintype.card BG*T)
            (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
          q rho Vs V mu K T zeta theta (physicalAlternatingSign start) k
          (sourceOriginalRootPhaseGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T phi F n (start+1)
            (offset+Fintype.card BG*T+Fintype.card BG*(J+ell))))) ≤ _
    rw [hoff]
    calc
      _ ≤ gamma^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu EF := hg
      _ ≤ gamma^2*((a start)^2*
          sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu H) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ ≤ gamma^2*((a start)^2*((sourceOriginalRootEnergyBudget434 gamma a n (start+1))^2*
          sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by simp only [sourceOriginalRootEnergyBudget434]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


/-- A fixed unmarked E owner is exactly the original full unphased E.
The local phase never leaves the ordered sum or its orbit average. -/
theorem source_original_root_FOREST_E_ENERGY434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (T initial A : ℕ)
    (S : Finset ℕ) (p : SourceOriginalRootForest434 A)
    (h : Fin A → (S ⊕ Fin A) → Bool) (lo hi : ℝ)
    (hFull : ∀ i (F : Output → ℂ),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      lo^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F)
    (hPhase : ∀ i
      (phase : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ),
      (∀ x z,‖phase x z‖ ≤ 1) → ∀ F : Output → ℂ,
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True) phase q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      hi^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F)
    (i : ℕ) (F : Output → ℂ) :
    let marked := sourceOriginalRootMarkedOwners434
      (sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))) p
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
        (fun _ _ => True)
        (fun x z => sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h)
          (initial+i*(Fintype.card BG*T+Fintype.card BG*(J+ell))+Fintype.card BG*T)
          (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
        q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
    (if i∈marked then hi else lo)^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  dsimp only
  by_cases hm : i∈sourceOriginalRootMarkedOwners434
      (sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))) p
  · rw [if_pos hm]
    apply hPhase
    intro x z
    rw [source_original_root_LIST_PHASE_UNIT434 _ (source_original_root_FOREST_SLOT_UNIT434 S p h)]
  · rw [if_neg hm]
    have he :
        (fun (x : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) =>
          sourceOriginalRootListPhase434 (sourceOriginalRootForestSlotPhase434 S p h)
            (initial+i*(Fintype.card BG*T+Fintype.card BG*(J+ell))+Fintype.card BG*T)
            (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z)) =
        (fun _ _ => (1:ℂ)) := by
      funext x z
      exact source_original_root_UNMARKED_E_LIST_PHASE434 S p h initial (Fintype.card BG*T)
        (Fintype.card BG*(J+ell)) i _ (source_original_root_E_PAD_LENGTH434
          SP sm BP bm J ell m cap patterns x z) hm
    rw [he]
    have hop :
        sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True) (fun _ _ => 1) q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F =
        sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F := by
      funext Y
      exact source_original_edge_PHASE_ONE_FULL434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F Y
    rw [hop]
    exact hFull i F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)



/-- Actual original forest scalar estimate from ONLY the two local E
energy banks. All phase and chain savings in the proof are derived.
The budget charges at most two potential E owners per selected edge;
the source high-rank pinned identification is a separate obligation. -/
theorem source_original_root_FOREST_FINITE_BOUND434
    (q rho vmax : ℝ) (R T A : ℕ)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (p : SourceOriginalRootForest434 A)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho) (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    let mu := physicalSourceMuTilde BP bm q (2*R) V
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
    let initial := Fintype.card BG*(J+ell)
    let marked := sourceOriginalRootMarkedOwners434
      (sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))) p
    (∀ g p,0 < mu g p) → (∀ g,∑ p,mu g p ≤ 2) →
    (∀ i (F : Output → ℂ),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      lo^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) →
    (∀ i
      (phase : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ),
      (∀ x z,‖phase x z‖ ≤ 1) → ∀ F : Output → ℂ,
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True) phase q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      hi^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) →
    ‖sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListForestTerm434 p)‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      (sourceOriginalRootEnergyBudget434 gamma (fun i => if i∈marked then hi else lo) (2*R) 0 *
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
          (physicalVacuum SP sm BP bm J ell)) := by
  dsimp only
  intro hmu hmass hFull hPhase
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  let W := max 1 vmax
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
  let initial := Fintype.card BG*(J+ell)
  let S := sourceOriginalRootActualAlphabet434 BP bm
  let marked := sourceOriginalRootMarkedOwners434
    (sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))) p
  let a := fun i => if i∈marked then hi else lo
  let B := sourceOriginalRootEnergyBudget434 gamma a (2*R) 0
  have hB : 0 ≤ B := source_original_root_ENERGY_BUDGET_NONNEG434 gamma a
    (Real.exp_pos _).le (fun i => by dsimp [a]; split_ifs <;> assumption) _ _
  rw [source_original_root_FOREST_TERM_AVERAGE434 SP sm BP bm J ell m cap patterns
    q rho Vs V K zeta theta k R T A hA p]
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  apply source_original_root_UNIT_AVERAGE_BOUND434
    (sourceOriginalRootForestCenter434 S p) _ (source_original_root_FOREST_CENTER_UNIT434 S p)
  intro h
  apply source_original_root_PHASE_BOUNDARY434 SP sm BP bm J ell m cap patterns
    q rho Vs hVs V K zeta theta k R T hmu
    (sourceOriginalRootForestSlotPhase434 S p h) (source_original_root_FOREST_SLOT_UNIT434 S p h)
    B hB
  have hh := source_original_root_PHASE_CHAIN_ENERGY434 SP sm BP bm J ell m cap patterns
    q rho vmax (2*R) T initial hq hq1 hquarter hr1 Vs hVs V hV hVW mu hmu hmass K zeta theta k
    (sourceOriginalRootForestSlotPhase434 S p h) (source_original_root_FOREST_SLOT_UNIT434 S p h) a
    (fun i F => source_original_root_FOREST_E_ENERGY434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k T initial A S p h lo hi hFull hPhase i F)
    (physicalVacuum SP sm BP bm J ell) (2*R) 0
  simpa only [Nat.zero_mul,Nat.add_zero] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootRankAssembly -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_original_root_ADDRESS_COUNT_ADD434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (o u v : ℕ) :
    sourceOriginalRootAddressCount434 p o (u+v)=
      sourceOriginalRootAddressCount434 p o u+sourceOriginalRootAddressCount434 p (o+u) v := by
  unfold sourceOriginalRootAddressCount434
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]

theorem source_original_root_FULL_ADDRESS_RANK434
    {A : ℕ} (p : SourceOriginalRootForest434 A) :
    sourceOriginalRootAddressCount434 p 0 A=sourceOriginalRootForestRank434 p := by
  unfold sourceOriginalRootAddressCount434 sourceOriginalRootForestRank434
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.zero_add]
  simp only [sourceOriginalRootParentAt434,dif_pos i.isLt]
  change (if ((p i).map Fin.val).isSome then 1 else 0)=(p i).elim 0 (fun _ => 1)
  cases hp : p i <;> simp

theorem source_original_root_INITIAL_ADDRESS_ZERO434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (o : ℕ) (ho : o ≤ A)
    (hp : ∀ i : Fin A,i.val < o → p i=none) :
    sourceOriginalRootAddressCount434 p 0 o=0 := by
  unfold sourceOriginalRootAddressCount434
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < o := Finset.mem_range.mp hj
  have hA : j < A := hj'.trans_le ho
  rw [Nat.zero_add]
  simp only [sourceOriginalRootParentAt434,dif_pos hA,hp ⟨j,hA⟩ hj']
  rfl

theorem source_original_root_BATCH_RANK_ADDRESSES434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T n o : ℕ) :
    sourceOriginalRootBatchRank434 p G M T n o=
      sourceOriginalRootAddressCount434 p o ((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M)) := by
  induction n generalizing o with
  | zero =>
    simp only [sourceOriginalRootBatchRank434,source_original_root_G_COUNT_ADDRESSES434,
      Nat.zero_add,Nat.one_mul,Nat.zero_mul,Nat.add_zero]
  | succ n ih =>
    simp only [sourceOriginalRootBatchRank434,source_original_root_G_COUNT_ADDRESSES434,
      source_original_root_E_COUNT_ADDRESSES434,ih]
    have hw : (n+1+1)*(Fintype.card G*T)+(n+1)*(Fintype.card G*M)=
        Fintype.card G*T+(Fintype.card G*M+((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))) := by ring
    rw [hw,source_original_root_ADDRESS_COUNT_ADD434 p o (Fintype.card G*T)
      (Fintype.card G*M+((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))),
      source_original_root_ADDRESS_COUNT_ADD434 p (o+Fintype.card G*T) (Fintype.card G*M)
      ((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))]
    omega

theorem source_original_root_BATCH_RANK_FULL434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T n o : ℕ)
    (hA : A=o+(n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))
    (hp : ∀ i : Fin A,i.val < o → p i=none) :
    sourceOriginalRootBatchRank434 p G M T n o=sourceOriginalRootForestRank434 p := by
  rw [source_original_root_BATCH_RANK_ADDRESSES434]
  have ho : o ≤ A := by omega
  have hh := source_original_root_ADDRESS_COUNT_ADD434 p 0 o
    ((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))
  have hw : o+((n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))=A := by omega
  rw [hw,source_original_root_FULL_ADDRESS_RANK434,
    source_original_root_INITIAL_ADDRESS_ZERO434 p o ho hp,Nat.zero_add,Nat.zero_add] at hh
  exact hh.symm

/-- Initial ND is a retained boundary mask. Nonzero initial constraints
therefore justify the full-rank exponent; no injective underlying array is assumed. -/
theorem source_original_root_SURVIVING_BATCH_RANK434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (G : Type) [Fintype G] [DecidableEq G] (M T n : ℕ) (H : List (Option ℕ))
    (hA : A=H.length+(n+1)*(Fintype.card G*T)+n*(Fintype.card G*M))
    (hND : (H.filterMap id).Nodup) (hNZ : sourceOriginalRootForestPrefix434 p H ≠ 0) :
    sourceOriginalRootBatchRank434 p G M T n H.length=sourceOriginalRootForestRank434 p := by
  apply source_original_root_BATCH_RANK_FULL434 p G M T n H.length hA
  intro i hi
  cases hp : p i with
  | none => rfl
  | some j => exact False.elim (hNZ (source_original_root_INITIAL_FOREST_ZERO434 p H hND i j hp hi))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualRankSuffix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


/-- Literal constrained suffix INCLUDING its retained initial factor.
Every forest is covered: selected initial children vanish, and all other
selected children are charged by the actual pinned rows. -/
theorem source_original_root_ACTUAL_RANK_SUFFIX434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (q rho W w delta a : ℝ) (N T : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hd : 0 ≤ delta) (ha : 0 ≤ a)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (hmu : ∀ g p,0 < mu g p) (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤ delta*(∑ p : BP g,mu g p))
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (hrow : ∀ i Q pin x,
      sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap patterns
        Q pin w q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
        zeta theta (physicalAlternatingSign i) k x ≤
      (delta^(∑ g,(Q g).card)*a)*w^(∑ g,(x.2 g).2.1.val))
    (terminal : Output → List (Option ℕ) → ℂ)
    (hterminal : ∀ Y H,‖terminal Y H‖ ≤ w^(∑ g,(Y.2 g).2.card))
    (n i : ℕ) (Y : Output) (H : List (Option ℕ))
    (hA : A=H.length+(n+1)*(Fintype.card BG*T)+n*(Fintype.card BG*(J+ell)))
    (hND : (H.filterMap id).Nodup) :
    ‖sourceOriginalRootForestPrefix434 p H*
      sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap patterns
      p q rho Vs V mu K zeta theta k N T terminal n i Y H‖ ≤
    delta^(sourceOriginalRootForestRank434 p)*
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^(n+1)*a^n*w^(∑ g,(Y.2 g).2.card) := by
  have hpos : 0 ≤ delta^(sourceOriginalRootForestRank434 p)*
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^(n+1)*a^n*w^(∑ g,(Y.2 g).2.card) := by
    positivity
  by_cases hz : sourceOriginalRootForestPrefix434 p H=0
  · simpa only [hz,zero_mul,norm_zero] using hpos
  have hPrefix : sourceOriginalRootForestPrefix434 p H=1 := by
    have he : sourceOriginalRootForestPrefix434 p H=sourceOriginalRootForestBatch434 p 0 H := by
      simp only [sourceOriginalRootForestPrefix434,sourceOriginalRootForestBatch434,Nat.zero_le,true_and]
    rw [he]
    exact source_original_root_FOREST_BATCH_NONZERO_ONE434 p 0 H (by rw [←he]; exact hz)
  rw [hPrefix,one_mul]
  have hh := source_original_root_ACTUAL_FOREST_SUFFIX434 SP sm BP bm J ell m cap patterns
    p q rho W w delta a N T hq hq1 hr hW hw hd ha hcontrol Vs V mu hVs hV hVW
    hmu hmass hAtom K zeta theta k hrow terminal hterminal n i Y H (by omega)
  rw [source_original_root_BATCH_BUDGET_CLOSED434,
    source_original_root_SURVIVING_BATCH_RANK434 p BG (J+ell) T n H hA hND hz] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootRankBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_root_ENERGY_BUDGET_PRODUCT434
    (gamma : ℝ) (a : ℕ → ℝ) (n i : ℕ) :
    sourceOriginalRootEnergyBudget434 gamma a n i=
      gamma^(n+1)*∏ j∈Finset.range n,a (i+j) := by
  induction n generalizing i with
  | zero => simp [sourceOriginalRootEnergyBudget434]
  | succ n ih =>
    rw [sourceOriginalRootEnergyBudget434,ih,Finset.prod_range_succ']
    simp only [Nat.add_zero]
    have he : (fun j : ℕ => a (i+1+j))=(fun j => a (i+(j+1))) := by
      funext j
      congr 1
      omega
    rw [he,pow_succ]
    ring

/-- A finite marked-set bound with no division by the small contraction.
The extra cost b is paid only at selected owners. -/
theorem source_original_root_MARKED_BUDGET434
    (gamma lo b : ℝ) (hg : 0 ≤ gamma) (hl : 0 ≤ lo) (hb : 1 ≤ b)
    (S : Finset ℕ) (n : ℕ) :
    sourceOriginalRootEnergyBudget434 gamma
      (fun i => lo*(if i∈S then b else 1)) n 0 ≤
      gamma^(n+1)*lo^n*b^S.card := by
  rw [source_original_root_ENERGY_BUDGET_PRODUCT434]
  simp only [Nat.zero_add,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
  have hprod :
      (∏ j∈Finset.range n,if j∈S then b else (1:ℝ)) =
      b^((Finset.range n).filter (fun j => j∈S)).card := by
    rw [Finset.card_filter,←Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hs : j∈S <;> simp [hs]
  rw [hprod,←mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hg _) (pow_nonneg hl _))
  apply pow_le_pow_right₀ hb
  apply Finset.card_le_card
  intro j hj
  exact (Finset.mem_filter.mp hj).2

theorem source_original_root_FOREST_RANK_BUDGET434
    {A : ℕ} (p : SourceOriginalRootForest434 A) (owner : ℕ → ℕ)
    (gamma lo b : ℝ) (hg : 0 ≤ gamma) (hl : 0 ≤ lo) (hb : 1 ≤ b) (n : ℕ) :
    sourceOriginalRootEnergyBudget434 gamma
      (fun i => lo*(if i∈sourceOriginalRootMarkedOwners434 owner p then b else 1)) n 0 ≤
      gamma^(n+1)*lo^n*b^(2*sourceOriginalRootForestRank434 p) := by
  apply (source_original_root_MARKED_BUDGET434 gamma lo b hg hl hb _ n).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (pow_nonneg hg _) (pow_nonneg hl _))
  exact pow_le_pow_right₀ hb (source_original_root_FOREST_OWNER_COUNT434 owner p)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestRankBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)



theorem source_original_root_FOREST_RANK_FINITE_BOUND434
    (q rho vmax : ℝ) (R T A : ℕ)
    (hA : A=(2*R+1)*Fintype.card BG*(J+ell+T))
    (p : SourceOriginalRootForest434 A)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho) (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (lo b : ℝ) (hlo : 0 ≤ lo) (hb : 1 ≤ b) :
    let mu := physicalSourceMuTilde BP bm q (2*R) V
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
    let initial := Fintype.card BG*(J+ell)
    let marked := sourceOriginalRootMarkedOwners434
      (sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))) p
    (∀ g p,0 < mu g p) → (∀ g,∑ p,mu g p ≤ 2) →
    (∀ i (F : Output → ℂ),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      lo^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) →
    (∀ i
      (phase : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ),
      (∀ x z,‖phase x z‖ ≤ 1) → ∀ F : Output → ℂ,
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True) phase q rho Vs V mu K T zeta theta (physicalAlternatingSign i) k F) ≤
      (lo*b)^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) →
    ‖sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T (sourceOriginalRootListForestTerm434 p)‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (physicalVacuum SP sm BP bm J ell) *
      gamma^(2*R+1)*lo^(2*R)*b^(2*sourceOriginalRootForestRank434 p) := by
  dsimp only
  intro hmu hmass hFull hPhase
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  let W := max 1 vmax
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  let gamma := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
  let initial := Fintype.card BG*(J+ell)
  let owner := sourceOriginalRootVisitOwner434 initial (Fintype.card BG*T) (Fintype.card BG*(J+ell))
  let marked := sourceOriginalRootMarkedOwners434 owner p
  let Bvac := sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
    (physicalVacuum SP sm BP bm J ell)
  have hvac : 0 ≤ Bvac := Finset.sum_nonneg (fun Y hY => mul_nonneg
    (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu Y hY).le (sq_nonneg _))
  have hh := source_original_root_FOREST_FINITE_BOUND434 SP sm BP bm J ell m cap patterns
    q rho vmax R T A hA p hq hq1 hquarter hr1 Vs hVs V hV hVW K zeta theta k
    lo (lo*b) hlo (mul_nonneg hlo (zero_le_one.trans hb)) hmu hmass hFull hPhase
  have he : (fun i : ℕ => if i∈marked then lo*b else lo)=
      (fun i => lo*(if i∈marked then b else 1)) := by
    funext i
    by_cases hi : i∈marked <;> simp [hi]
  change _ ≤ ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖*
    (sourceOriginalRootEnergyBudget434 gamma (fun i => if i∈marked then lo*b else lo) (2*R) 0*Bvac) at hh
  rw [he] at hh
  have hbudget := source_original_root_FOREST_RANK_BUDGET434 p owner gamma lo b
    (Real.exp_pos _).le hlo hb (2*R)
  apply hh.trans
  calc
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖*
        ((gamma^(2*R+1)*lo^(2*R)*b^(2*sourceOriginalRootForestRank434 p))*Bvac) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbudget hvac) (norm_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourceRankSuffix -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Actual SOURCE forest suffix. Pins and local masks are the literal
forest constraints; the ordered pinned E bound and atom law are discharged.
The retained initial factor covers all forests, including annihilated
initial edges. The exponent is the full forest rank. -/
theorem eventually_source_original_root_SOURCE_RANK_SUFFIX434
    (c vmin q rho W w : ℝ) (hc : 0 < c) (hv : 0 < vmin)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hW : 1 ≤ W) (hw : 1 ≤ w)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p∈P g}),NeZero p.val]
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ)=V g)
      (hBig : ∀ g (p : {p : ℕ // p∈P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (conductor : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
      (hhA : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (cap : G → ℕ),
    let BP := fun g => {p : ℕ // p∈P g}
    let bm := fun (g : G) (p : BP g) => p.val
    let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
    let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
    let delta := 2/(vmin*Real.exp (L^c))
    let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi

    ∀ {A : ℕ} (p : SourceOriginalRootForest434 A)
      (zeta theta : ℝ) (k : ℤ) (n i : ℕ)
      (Y : FullPhysicalOutput SP sm BP bm (J+ell)) (H : List (Option ℕ))
      (hSize : A=H.length+(n+1)*(Fintype.card G*(Nat.ceil (L^2)))+
        n*(Fintype.card G*(J+ell)))
      (hND : (H.filterMap id).Nodup),
    ‖sourceOriginalRootForestPrefix434 p H*
      sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap pat
      p q rho Vs V mu K zeta theta k (2*Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))
      (fun out _ => physicalVacuum SP sm BP bm J ell out) n i Y H‖ ≤
    delta^(sourceOriginalRootForestRank434 p)*
      (Real.exp (4*W*w*(Fintype.card G:ℝ)/rho))^(n+1)*a^n*w^(∑ g,(Y.2 g).2.card) := by
  filter_upwards [eventually_source_original_forest_SOURCE_E_PINNED434
    c vmin q rho hc hv hq hq1 hr hr1,
    eventually_source_original_forest_TILT_LAWS434 c vmin q hc hv hq.le hq1.le] with L hE hTilt
  intro SG instSG instDSG SP instSP instDSP sm instSM G instG instDG P instP
    V hV hVW hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi hhA hhB hxi cap
  dsimp only
  intro A p zeta theta k n i Y H hSize hND
  let BP := fun g => {p : ℕ // p∈P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
  let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
  let delta := 2/(vmin*Real.exp (L^c))
  let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP bm V (fun g => Subtype.val_injective) hV hHarmonic hBig
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hd : 0 ≤ delta := by dsimp [delta]; positivity
  have ha : 0 ≤ a := source_original_root_PINNED_ROW_BUDGET_NONNEG434
    Vs V blockA blockB ell m conductor q rho w xi hVs hq1.le hr1.le hw0.le
  have hrow (j : ℕ) (Q : G → Finset (Fin (J+ell))) (pin : G → Fin (J+ell) → ℕ)
      (x : FullPhysicalState SP sm BP bm (J+ell) cap) :
      sourceOriginalForestEPinnedRow434 SP sm BP bm J ell m cap pat
        Q pin w q rho Vs V mu (memoryOrientationK BP J ell m pat K (physicalAlternatingSign j))
        zeta theta (physicalAlternatingSign j) k x ≤
      (delta^(∑ g,(Q g).card)*a)*w^(∑ g,(x.2 g).2.1.val) := by
    have ho : physicalAlternatingSign j=1 ∨ physicalAlternatingSign j= -1 := by
      unfold physicalAlternatingSign
      split_ifs <;> simp
    exact hE SP sm P V hV hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi
      hhA hhB hxi cap Q pin w hw zeta theta (physicalAlternatingSign j) k ho x
  have hterminal (Y : FullPhysicalOutput SP sm BP bm (J+ell)) (_H : List (Option ℕ)) :
      ‖physicalVacuum SP sm BP bm J ell Y‖ ≤ w^(∑ g,(Y.2 g).2.card) := by
    unfold physicalVacuum
    split_ifs
    · simpa only [norm_one] using (one_le_pow₀ hw : (1:ℝ) ≤ w^(∑ g,(Y.2 g).2.card))
    · simp only [norm_zero]
      positivity

  have hh := source_original_root_ACTUAL_RANK_SUFFIX434 SP sm BP bm J ell m cap pat
    p q rho W w delta a (2*Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))
    hq.le hq1.le hr hW hw0 hd ha hcontrol Vs V mu hVs
    (fun g => (hv.trans_le (hV g)).le) hVW hmu hmass hAtom K zeta theta k hrow
    (fun out _ => physicalVacuum SP sm BP bm J ell out) hterminal n i Y H hSize hND
  exact hh
end Green64Analytic.CorrelationSquare

end

end

