module

public import Green64.Library.Weights.RetiredTerminalEnergy
public import Green64.Library.Weights.Part074

@[expose] public section

/-!
# Weights / RetiredSourceGlobalBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredSourceGlobalBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

/-- One gauge for the entire numerical prime pool, fixed throughout
all visits. It changes the norm, not the original source parameters. -/
def sourceOriginalRetiredCriticalTau434 (n M : ℝ) : ℝ := n / ((n+1)*M)

theorem source_original_RETIRED_critical_boundary434
    (n M : ℝ) (hn : 0 < n) (hM : 0 < M) :
    0 < sourceOriginalRetiredCriticalTau434 n M ∧
    sourceOriginalRetiredCriticalTau434 n M * M < 1 ∧
    1/(1-sourceOriginalRetiredCriticalTau434 n M*M) = n+1 := by
  have hnp : 0 < n+1 := by linarith
  have ht : 0 < sourceOriginalRetiredCriticalTau434 n M :=
    div_pos hn (mul_pos hnp hM)
  have he : sourceOriginalRetiredCriticalTau434 n M * M = n/(n+1) := by
    unfold sourceOriginalRetiredCriticalTau434
    field_simp
  have hlt : n/(n+1) < 1 := (div_lt_one hnp).mpr (by linarith)
  refine ⟨ht,he ▸ hlt,?_⟩
  rw [he]
  field_simp
  <;> ring

private theorem point_tilt (A n p : ℝ) (hA : 0 ≤ A) (hAn : A ≤ n)
    (hn : 1 ≤ n) (hp : 4*n^2 ≤ p) :
    0 < 1-A/p ∧
    1/(p*(1-A/p)) ≤ 2/p ∧
    2*A*(1/(p*(1-A/p))-1/p) ≤ 1/p := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hp0 : 0 < p := (mul_pos (by norm_num) (sq_pos_of_pos hn0)).trans_le hp
  have hA2 := pow_le_pow_left₀ hA hAn 2
  have hpa : 2*A ≤ p := by nlinarith [sq_nonneg (n-1)]
  have hd : 0 < p-A := by linarith
  have hb : 0 < 1-A/p := by
    apply sub_pos.mpr
    apply (div_lt_one hp0).mpr
    linarith
  have hid : 1/(p*(1-A/p)) = 1/(p-A) := by
    congr 1
    field_simp
  refine ⟨hb,?_,?_⟩
  · rw [hid]
    exact (div_le_div_iff₀ hd hp0).mpr (by linarith)
  · have hdiff : 2*A*(1/(p-A)-1/p) = (2*A^2)/(p*(p-A)) := by
      field_simp
      <;> ring
    rw [hid,hdiff]
    have hc : 2*A^2 ≤ p-A := by nlinarith [sq_nonneg (n-1)]
    have hm := mul_le_mul_of_nonneg_left hc hp0.le
    apply (div_le_div_iff₀ (mul_pos hp0 hd) hp0).mpr
    nlinarith only [hm]

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]

/-- Exact total of V_g*mu-tilde, across ALL source BIG groups. -/
def sourceOriginalRetiredTiltedMass434 (q : ℝ) (N : ℕ) : ℝ :=
  ∑ g, ∑ p : BP g, 1/((bm g p : ℝ)*physicalSourceBaseline BP bm q N g p)

def sourceOriginalRetiredSourceTau434 (q : ℝ) (N : ℕ) : ℝ :=
  sourceOriginalRetiredCriticalTau434 ((N+1 : ℕ) : ℝ)
    (sourceOriginalRetiredTiltedMass434 BP bm q N)

/-- Baseline times the squared-energy costs of all N+1 genuine G
visits in the COMMON retired gauge. This includes both endpoints. -/
def sourceOriginalRetiredGlobalGBudget434 (q : ℝ) (N : ℕ) : ℝ :=
  (physicalSourceBaselineProduct BP bm q N)^2 *
    Real.exp ((∑ i ∈ Finset.range (N+1), sourceVisitEta q N i) *
      (sourceOriginalRetiredTiltedMass434 BP bm q N +
        1/sourceOriginalRetiredSourceTau434 BP bm q N))

/-- This is the literal tilted harmonic mass, independently of the
choice of positive group harmonic normalizations. -/
theorem source_original_RETIRED_source_mass_exact434
    (q : ℝ) (N : ℕ) (V : BG → ℝ) (hV : ∀ g, 0 < V g) :
    (∑ g, ∑ p : BP g, V g*physicalSourceMuTilde BP bm q N V g p) =
      sourceOriginalRetiredTiltedMass434 BP bm q N := by
  unfold sourceOriginalRetiredTiltedMass434
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro p hp
  unfold physicalSourceMuTilde
  field_simp [(hV g).ne']

/-- A real source budget, not an iterated positive CLEAN estimate:
the common retired gauge and ONE original baseline cost only exp(3H),
where H is the true UNTILTED full-BIG harmonic mass. -/
theorem source_original_RETIRED_source_global_G_budget434
    [Nonempty (Sigma BP)]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (hSize : ∀ g p, 4*(((N+1 : ℕ) : ℝ))^2 ≤ (bm g p : ℝ)) :
    0 < sourceOriginalRetiredSourceTau434 BP bm q N ∧
    sourceOriginalRetiredSourceTau434 BP bm q N *
      sourceOriginalRetiredTiltedMass434 BP bm q N < 1 ∧
    1/(1-sourceOriginalRetiredSourceTau434 BP bm q N *
      sourceOriginalRetiredTiltedMass434 BP bm q N) = ((N+2 : ℕ) : ℝ) ∧
    sourceOriginalRetiredGlobalGBudget434 BP bm q N ≤
      Real.exp (3*(∑ g, ∑ p : BP g, 1/(bm g p : ℝ))) := by
  let n : ℝ := ((N+1 : ℕ) : ℝ)
  let A := ∑ i ∈ Finset.range (N+1), sourceVisitEta q N i
  let H := ∑ g, ∑ p : BP g, 1/(bm g p : ℝ)
  let M := sourceOriginalRetiredTiltedMass434 BP bm q N
  have hn : 1 ≤ n := by dsimp [n]; norm_num
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hA := source_original_B26_visit_sum_unit434 q hq hq1 N
  have hp (g : BG) (p : BP g) : 0 < (bm g p : ℝ) :=
    Nat.cast_pos.mpr (NeZero.pos _)
  have hpt (g : BG) (p : BP g) :=
    point_tilt A n (bm g p : ℝ) hA.1 hA.2 hn (hSize g p)
  have hb (g : BG) (p : BP g) : 0 < physicalSourceBaseline BP bm q N g p :=
    (hpt g p).1
  have hl (g : BG) (p : BP g) :
      0 < 1/((bm g p : ℝ)*physicalSourceBaseline BP bm q N g p) :=
    one_div_pos.mpr (mul_pos (hp g p) (hb g p))
  have hM : 0 < M := by
    let z : Sigma BP := Classical.choice inferInstance
    have hg : 0 < ∑ p : BP z.1,
        1/((bm z.1 p : ℝ)*physicalSourceBaseline BP bm q N z.1 p) :=
      Finset.sum_pos' (fun p hp => (hl z.1 p).le) ⟨z.2,Finset.mem_univ _,hl z.1 z.2⟩
    exact hg.trans_le (Finset.single_le_sum
      (f := fun g => ∑ p : BP g, 1/((bm g p : ℝ)*physicalSourceBaseline BP bm q N g p))
      (fun g hg => Finset.sum_nonneg (fun p hp => (hl g p).le)) (Finset.mem_univ z.1))
  have hM2 : M ≤ 2*H := by
    calc
      _ ≤ ∑ g, ∑ p : BP g, 2/(bm g p : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        exact Finset.sum_le_sum (fun p hp => (hpt g p).2.1)
      _ = _ := by simp only [H, div_eq_mul_inv, one_mul, Finset.mul_sum]
  have hd : 2*A*(M-H) ≤ H := by
    calc
      _ = ∑ g, ∑ p : BP g, 2*A*
          (1/((bm g p : ℝ)*physicalSourceBaseline BP bm q N g p)-1/(bm g p : ℝ)) := by
        simp only [M,H,sourceOriginalRetiredTiltedMass434,
          Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
      _ ≤ _ := Finset.sum_le_sum (fun g hg =>
        Finset.sum_le_sum (fun p hp => (hpt g p).2.2))
  have hc := source_original_RETIRED_critical_boundary434 n M hn0 hM
  refine ⟨hc.1,hc.2.1,?_,?_⟩
  · change 1/(1-sourceOriginalRetiredCriticalTau434 n M*M) = ((N+2 : ℕ) : ℝ)
    rw [hc.2.2]
    dsimp only [n]
    push_cast
    ring
  · have hb0 : 0 ≤ physicalSourceBaselineProduct BP bm q N :=
      Finset.prod_nonneg (fun g hg => Finset.prod_nonneg (fun p hp => (hb g p).le))
    have hbexp : physicalSourceBaselineProduct BP bm q N ≤ Real.exp (-A*H) := by
      calc
        _ ≤ ∏ g, ∏ p : BP g, Real.exp (-A/(bm g p : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro g hg
            exact Finset.prod_nonneg (fun p hp => (hb g p).le)
          · intro g hg
            apply Finset.prod_le_prod₀
            · intro p hp
              exact (hb g p).le
            · intro p hp
              simpa only [physicalSourceBaseline,A,sub_eq_add_neg,neg_div,add_comm] using
                Real.add_one_le_exp (-A/(bm g p : ℝ))
        _ = _ := by simp only [H,Real.exp_sum,Finset.mul_sum,div_eq_mul_inv,one_mul,neg_mul]
    have hinv : A/sourceOriginalRetiredSourceTau434 BP bm q N =
        A*M+(A/n)*M := by
      change A/(n/((n+1)*M)) = _
      field_simp
      <;> ring
    have hcrit : A/sourceOriginalRetiredSourceTau434 BP bm q N ≤ A*M+M := by
      rw [hinv]
      have hh : (A/n)*M ≤ M :=
        mul_le_of_le_one_left hM.le ((div_le_one hn0).mpr hA.2)
      linarith
    have hexp : -2*A*H + A*(M+1/sourceOriginalRetiredSourceTau434 BP bm q N) ≤ 3*H := by
      simp only [div_eq_mul_inv] at hcrit ⊢
      nlinarith only [hd,hM2,hcrit]
    unfold sourceOriginalRetiredGlobalGBudget434
    calc
      _ ≤ (Real.exp (-A*H))^2 *
          Real.exp (A*(M+1/sourceOriginalRetiredSourceTau434 BP bm q N)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb0 hbexp 2) (Real.exp_pos _).le
      _ = Real.exp (-2*A*H+A*(M+1/sourceOriginalRetiredSourceTau434 BP bm q N)) := by
        rw [pow_two, ←Real.exp_add, ←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hexp

end Green64Analytic.CorrelationSquare

end

end

