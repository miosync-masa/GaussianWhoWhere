import GaussianWhoWhere.PolynomialRigidity
import GaussianWhoWhere.HermitePochhammer

/-!
# Level 2G — General finite Hermite–Pochhammer uniqueness

We extend `finite_concrete_uniqueness_P16` (Level 2 truncation up to
`P₁₆`) to arbitrary finite truncation `K`:

  `Q_K(x) := 1 + Σ_{k = 0}^{K - 1} c_k · P_{4(k+1)}(x)`

  (so the `k`-th term uses `P2nPoly (2(k+1))`, ranging over
  `P₄, P₈, P₁₂, …, P_{4K}`)

If `Q_K(x + y) = Q_K(x) · Q_K(y)` for all `x y` (or, equivalently for
the polynomial layer, `Q_K(0) = 1` and a single nonzero translation
identity), then every `c_k = 0`.

The proof has three layers:

1. **Degree / leading coefficient of `P2nPoly`.** `P2nPoly n` has
   `natDegree n` and `leadingCoeff 2^(2n)`. This pins down which
   summand contributes to the highest degree.

2. **Translation rigidity wrapper.** Apply
   `polynomial_translation_rigidity` to `QFinitePoly K c`.

3. **Coefficient peeling.** Compare `coeff (2K)` on
   `QFinitePoly K c = 1`. Only the top summand has a nonzero
   contribution at degree `2K`, forcing `c_{K-1} = 0`. Then strong
   induction on `K`. -/

noncomputable section

namespace GaussianWhoWhere

open Polynomial

/-! ## Layer 1: degree and leading coefficient of `P2nPoly`. -/

private theorem natDegree_halfX : halfX.natDegree = 1 := by
  unfold halfX
  rw [natDegree_C_mul_X]
  norm_num

private theorem leadingCoeff_halfX : halfX.leadingCoeff = (1 : ℝ) / 2 := by
  unfold halfX
  rw [leadingCoeff_C_mul_X]

private theorem natDegree_pochhammerHalfX (n : ℕ) :
    (pochhammerHalfX n).natDegree = n := by
  unfold pochhammerHalfX
  rw [natDegree_comp, ascPochhammer_natDegree, natDegree_halfX, mul_one]

private theorem leadingCoeff_pochhammerHalfX (n : ℕ) :
    (pochhammerHalfX n).leadingCoeff = ((1 : ℝ) / 2) ^ n := by
  unfold pochhammerHalfX
  by_cases hn : n = 0
  · subst hn; simp [ascPochhammer_zero]
  · have hne : (halfX.natDegree) ≠ 0 := by rw [natDegree_halfX]; exact one_ne_zero
    -- ascPochhammer ℝ n is monic.
    have hmonic : (ascPochhammer ℝ n).Monic := monic_ascPochhammer ℝ n
    rw [leadingCoeff_comp hne, leadingCoeff_halfX,
        hmonic.leadingCoeff, ascPochhammer_natDegree, one_mul]

private def P2nPolyTerm (n j : ℕ) : Polynomial ℝ :=
  Polynomial.C (hermiteEvenCoeff n j * (2 : ℝ) ^ j) * pochhammerHalfX j

private theorem P2nPoly_eq_sum_terms (n : ℕ) :
    P2nPoly n = ∑ j ∈ Finset.range (n + 1), P2nPolyTerm n j := by
  rfl

private theorem hermiteEvenCoeff_top (n : ℕ) :
    hermiteEvenCoeff n n = (2 : ℝ) ^ (2 * n) := by
  unfold hermiteEvenCoeff
  rw [if_pos (le_refl _)]
  have h1 : (n : ℕ) - n = 0 := Nat.sub_self n
  rw [h1]
  have hfac : ((Nat.factorial (2 * n) : ℝ) ≠ 0) := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hfac0 : (Nat.factorial 0 : ℝ) = 1 := by norm_num [Nat.factorial]
  rw [hfac0]
  field_simp

private theorem natDegree_P2nPolyTerm_le (n j : ℕ) :
    (P2nPolyTerm n j).natDegree ≤ j := by
  unfold P2nPolyTerm
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_pochhammerHalfX]

/-- Coefficient at degree `j` of the term `P2nPolyTerm n j` is the
top coefficient `hermiteEvenCoeff n j * 2^j * (1/2)^j`, which simplifies
to `hermiteEvenCoeff n j` after cancellation. -/
private theorem coeff_P2nPolyTerm_top_index (n j : ℕ) :
    (P2nPolyTerm n j).coeff j
      = hermiteEvenCoeff n j := by
  unfold P2nPolyTerm
  rw [coeff_C_mul]
  -- pochhammerHalfX j has natDegree j; coeff at j is its leading coefficient.
  have hcoeff : (pochhammerHalfX j).coeff j
      = (pochhammerHalfX j).leadingCoeff := by
    rw [Polynomial.leadingCoeff, natDegree_pochhammerHalfX]
  rw [hcoeff, leadingCoeff_pochhammerHalfX]
  -- (hermiteEvenCoeff n j * 2^j) * (1/2)^j = hermiteEvenCoeff n j.
  rw [mul_assoc]
  rw [show (2 : ℝ) ^ j * ((1 : ℝ) / 2) ^ j = 1 from by
        rw [div_pow, one_pow]
        field_simp]
  ring

/-- Top-degree coefficient of `P2nPoly n` equals
`hermiteEvenCoeff n n = 2^(2n)`. -/
theorem coeff_P2nPoly_top (n : ℕ) :
    (P2nPoly n).coeff n = (2 : ℝ) ^ (2 * n) := by
  rw [P2nPoly_eq_sum_terms, finset_sum_coeff]
  rw [Finset.sum_eq_single n]
  · -- main term j = n.
    rw [coeff_P2nPolyTerm_top_index, hermiteEvenCoeff_top]
  · -- other j: either j > n is excluded, or j < n gives natDegree < n.
    intro j hj hjn
    rcases lt_or_gt_of_ne hjn with hlt | hgt
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_P2nPolyTerm_le n j) hlt)
    · exact absurd (Finset.mem_range.mp hj) (by omega)
  · simp

private theorem natDegree_P2nPoly_le (n : ℕ) :
    (P2nPoly n).natDegree ≤ n := by
  rw [P2nPoly_eq_sum_terms]
  refine (natDegree_sum_le _ _).trans ?_
  -- (Finset.range (n+1)).sup (natDegree ∘ P2nPolyTerm n) ≤ n
  refine Finset.sup_le ?_
  intro j hj
  exact (natDegree_P2nPolyTerm_le n j).trans (by
    have := Finset.mem_range.mp hj
    omega)

theorem natDegree_P2nPoly (n : ℕ) : (P2nPoly n).natDegree = n := by
  refine le_antisymm (natDegree_P2nPoly_le n) ?_
  have hne : (P2nPoly n).coeff n ≠ 0 := by
    rw [coeff_P2nPoly_top]; positivity
  exact le_natDegree_of_ne_zero hne

theorem leadingCoeff_P2nPoly (n : ℕ) :
    (P2nPoly n).leadingCoeff = (2 : ℝ) ^ (2 * n) := by
  rw [Polynomial.leadingCoeff, natDegree_P2nPoly, coeff_P2nPoly_top]

/-! ## Layer 2: general truncation polynomial and translation rigidity. -/

/-- General finite Hermite–Pochhammer truncation polynomial:

  `QFinitePoly K c = 1 + Σ_{k : Fin K} c_k · P_{4(k+1)}`.

The `k`-th summand uses `P2nPoly (2 * (k.val + 1))`, ranging over
`P₄, P₈, P₁₂, …, P_{4K}`. -/
def QFinitePoly (K : ℕ) (c : Fin K → ℝ) : Polynomial ℝ :=
  1 + ∑ k : Fin K, Polynomial.C (c k) * P2nPoly (2 * (k.val + 1))

theorem QFinitePoly_eq_one_of_translation
    (K : ℕ) (c : Fin K → ℝ) (a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : (QFinitePoly K c).eval 0 = 1)
    (htrans : ∀ x : ℝ,
      (QFinitePoly K c).eval (x + a)
        = (QFinitePoly K c).eval a * (QFinitePoly K c).eval x) :
    QFinitePoly K c = 1 :=
  polynomial_translation_rigidity (QFinitePoly K c) a ha hQ0 htrans

/-! ## Layer 3: coefficient peeling.

The `k`-th summand `C (c k) * P2nPoly (2(k+1))` has natDegree
`2(k+1)`. Strictly increasing in `k`, so `coeff (2(K))` of
`QFinitePoly (K+1) c` is contributed only by the summand at `k = K`,
giving `c_K * 2^(4(K+1)) = 0` from comparing with `1.coeff (2(K)) = 0`. -/

private theorem natDegree_QFinitePoly_summand_le
    (K : ℕ) (c : Fin K → ℝ) (k : Fin K) :
    (Polynomial.C (c k) * P2nPoly (2 * (k.val + 1))).natDegree
      ≤ 2 * (k.val + 1) := by
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_P2nPoly]

theorem coeffs_zero_of_QFinitePoly_eq_one :
    ∀ (K : ℕ) (c : Fin K → ℝ),
      QFinitePoly K c = 1 → ∀ k : Fin K, c k = 0 := by
  intro K
  induction K with
  | zero =>
      intro _ _ k
      exact Fin.elim0 k
  | succ K ih =>
      intro c hQ
      set kTop : Fin (K + 1) := ⟨K, Nat.lt_succ_self K⟩ with hkTop_def
      -- coeff (2 * (K + 1)) of LHS = RHS = 1.
      have hcoeff_eq :
          (QFinitePoly (K + 1) c).coeff (2 * (K + 1))
            = (1 : Polynomial ℝ).coeff (2 * (K + 1)) :=
        congrArg (fun p : Polynomial ℝ => p.coeff (2 * (K + 1))) hQ
      have hone : (1 : Polynomial ℝ).coeff (2 * (K + 1)) = 0 := by
        rw [Polynomial.coeff_one]
        simp [show 2 * (K + 1) ≠ 0 from by omega]
      -- LHS coefficient at top degree = c kTop * 2^(4(K+1)).
      have hLHS :
          (QFinitePoly (K + 1) c).coeff (2 * (K + 1))
            = c kTop * (2 : ℝ) ^ (4 * (K + 1)) := by
        unfold QFinitePoly
        rw [coeff_add, hone, zero_add, finset_sum_coeff]
        rw [Finset.sum_eq_single kTop]
        · -- main term at kTop:
          -- coeff (2(K+1)) (C(c kTop) * P2nPoly (2(K+1))) =
          --   c kTop * coeff (2(K+1)) (P2nPoly (2(K+1)))
          --   = c kTop * 2^(2 * 2(K+1)) = c kTop * 2^(4(K+1)).
          rw [coeff_C_mul]
          have hKtop_val : kTop.val = K := rfl
          rw [show 2 * (kTop.val + 1) = 2 * (K + 1) from by rw [hKtop_val]]
          rw [coeff_P2nPoly_top]
          have h4k : 2 * (2 * (K + 1)) = 4 * (K + 1) := by ring
          rw [h4k]
        · intro k _ hk_ne
          -- k ≠ kTop ⇒ k.val < K ⇒ summand has natDegree ≤ 2(k.val + 1) < 2(K+1).
          have hk_lt : k.val < K := by
            have hkle : k.val ≤ K := by have := k.isLt; omega
            cases lt_or_eq_of_le hkle with
            | inl h => exact h
            | inr h => exact absurd (Fin.ext h : k = kTop) hk_ne
          apply coeff_eq_zero_of_natDegree_lt
          have hsum := natDegree_QFinitePoly_summand_le (K + 1) c k
          omega
        · simp
      -- c kTop = 0.
      have hpow_pos : (2 : ℝ) ^ (4 * (K + 1)) > 0 := by positivity
      have hctop : c kTop = 0 := by
        have heq : c kTop * (2 : ℝ) ^ (4 * (K + 1)) = 0 := by
          rw [← hLHS, hcoeff_eq, hone]
        exact (mul_eq_zero.mp heq).resolve_right (ne_of_gt hpow_pos)
      -- Build the smaller coefficient function and apply IH.
      let c' : Fin K → ℝ := fun k => c ⟨k.val, by omega⟩
      have hQ' : QFinitePoly K c' = 1 := by
        unfold QFinitePoly at hQ ⊢
        rw [Fin.sum_univ_castSucc] at hQ
        -- Top summand `C (c kTop) * P2nPoly (...)` is zero since c kTop = 0.
        have htop_term :
            Polynomial.C (c (Fin.last K)) * P2nPoly (2 * ((Fin.last K).val + 1)) = 0 := by
          have hlast : (Fin.last K) = kTop := rfl
          rw [hlast, hctop]; simp
        rw [htop_term, add_zero] at hQ
        -- The remaining sum, over Fin K via castSucc, equals the c'-sum.
        have hsum :
            ∑ i : Fin K, Polynomial.C (c i.castSucc)
                          * P2nPoly (2 * ((i.castSucc).val + 1))
              = ∑ k : Fin K, Polynomial.C (c' k)
                          * P2nPoly (2 * (k.val + 1)) := by
          apply Finset.sum_congr rfl
          intro k _
          show Polynomial.C (c k.castSucc) * P2nPoly (2 * (k.castSucc.val + 1))
              = Polynomial.C (c' k) * P2nPoly (2 * (k.val + 1))
          have : (k.castSucc).val = k.val := rfl
          rw [this]
          rfl
        rw [hsum] at hQ
        exact hQ
      have ih_concl : ∀ k : Fin K, c' k = 0 := ih c' hQ'
      -- Conclude for all k : Fin (K+1).
      intro k
      by_cases hk : k.val < K
      · have h := ih_concl ⟨k.val, hk⟩
        change c ⟨k.val, _⟩ = 0 at h
        have : k = ⟨k.val, by omega⟩ := Fin.ext rfl
        rw [this]
        exact h
      · have hk_eq : k.val = K := by have := k.isLt; omega
        have : k = kTop := Fin.ext hk_eq
        rw [this]; exact hctop

/-! ## Layer 4: combine into the general translation-uniqueness theorem. -/

/-- **General finite Hermite–Pochhammer uniqueness via translation
rigidity.** From `Q(0) = 1`, `a ≠ 0`, and the translation
factorization at `a`, every coefficient `c_k` of the truncation
polynomial vanishes. -/
theorem finite_general_uniqueness_of_translation
    (K : ℕ) (c : Fin K → ℝ) (a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : (QFinitePoly K c).eval 0 = 1)
    (htrans : ∀ x : ℝ,
      (QFinitePoly K c).eval (x + a)
        = (QFinitePoly K c).eval a * (QFinitePoly K c).eval x) :
    ∀ k : Fin K, c k = 0 :=
  coeffs_zero_of_QFinitePoly_eq_one K c
    (QFinitePoly_eq_one_of_translation K c a ha hQ0 htrans)

/-! ## Layer 5: full multiplicativity route (Q(0) ∈ {0, 1}).

If `QFinitePoly K c` is multiplicative for all `(x, y)` (a stronger
hypothesis than the single-translation version), then `Q(0) ∈ {0, 1}`.
The `Q(0) = 1` branch goes through translation rigidity directly. The
`Q(0) = 0` branch forces `QFinitePoly K c = 0` as a polynomial; the
same coefficient-peeling argument gives every `c_k = 0`, and the
remaining constant-term identity `(1 : Polynomial ℝ) = 0` fails. -/

/-- Coefficient peeling generalized: same argument works against any
constant polynomial `C const`, yielding all `c_k = 0`. -/
private theorem coeffs_zero_of_QFinitePoly_eq_C :
    ∀ (K : ℕ) (c : Fin K → ℝ) (const : ℝ),
      QFinitePoly K c = Polynomial.C const → ∀ k : Fin K, c k = 0 := by
  intro K
  induction K with
  | zero =>
      intro _ _ _ k; exact Fin.elim0 k
  | succ K ih =>
      intro c const hQ
      set kTop : Fin (K + 1) := ⟨K, Nat.lt_succ_self K⟩ with hkTop_def
      have hcoeff_eq :
          (QFinitePoly (K + 1) c).coeff (2 * (K + 1))
            = (Polynomial.C const).coeff (2 * (K + 1)) :=
        congrArg (fun p : Polynomial ℝ => p.coeff (2 * (K + 1))) hQ
      have hRHS : (Polynomial.C const).coeff (2 * (K + 1)) = 0 := by
        rw [Polynomial.coeff_C]
        simp [show 2 * (K + 1) ≠ 0 from by omega]
      have hLHS :
          (QFinitePoly (K + 1) c).coeff (2 * (K + 1))
            = c kTop * (2 : ℝ) ^ (4 * (K + 1)) := by
        unfold QFinitePoly
        rw [coeff_add, finset_sum_coeff]
        have hone : (1 : Polynomial ℝ).coeff (2 * (K + 1)) = 0 := by
          rw [Polynomial.coeff_one]
          simp [show 2 * (K + 1) ≠ 0 from by omega]
        rw [hone, zero_add]
        rw [Finset.sum_eq_single kTop]
        · rw [coeff_C_mul]
          have hKtop_val : kTop.val = K := rfl
          rw [show 2 * (kTop.val + 1) = 2 * (K + 1) from by rw [hKtop_val]]
          rw [coeff_P2nPoly_top]
          have h4k : 2 * (2 * (K + 1)) = 4 * (K + 1) := by ring
          rw [h4k]
        · intro k _ hk_ne
          have hk_lt : k.val < K := by
            have hkle : k.val ≤ K := by have := k.isLt; omega
            cases lt_or_eq_of_le hkle with
            | inl h => exact h
            | inr h => exact absurd (Fin.ext h : k = kTop) hk_ne
          apply coeff_eq_zero_of_natDegree_lt
          have hsum := natDegree_QFinitePoly_summand_le (K + 1) c k
          omega
        · simp
      have hpow_pos : (2 : ℝ) ^ (4 * (K + 1)) > 0 := by positivity
      have hctop : c kTop = 0 := by
        have heq : c kTop * (2 : ℝ) ^ (4 * (K + 1)) = 0 := by
          rw [← hLHS, hcoeff_eq, hRHS]
        exact (mul_eq_zero.mp heq).resolve_right (ne_of_gt hpow_pos)
      let c' : Fin K → ℝ := fun k => c ⟨k.val, by omega⟩
      have hQ' : QFinitePoly K c' = Polynomial.C const := by
        unfold QFinitePoly at hQ ⊢
        rw [Fin.sum_univ_castSucc] at hQ
        have htop_term :
            Polynomial.C (c (Fin.last K)) * P2nPoly (2 * ((Fin.last K).val + 1)) = 0 := by
          have hlast : (Fin.last K) = kTop := rfl
          rw [hlast, hctop]; simp
        rw [htop_term, add_zero] at hQ
        have hsum :
            ∑ i : Fin K, Polynomial.C (c i.castSucc)
                          * P2nPoly (2 * ((i.castSucc).val + 1))
              = ∑ k : Fin K, Polynomial.C (c' k)
                          * P2nPoly (2 * (k.val + 1)) := by
          apply Finset.sum_congr rfl
          intro k _
          show Polynomial.C (c k.castSucc) * P2nPoly (2 * (k.castSucc.val + 1))
              = Polynomial.C (c' k) * P2nPoly (2 * (k.val + 1))
          have : (k.castSucc).val = k.val := rfl
          rw [this]
          rfl
        rw [hsum] at hQ
        exact hQ
      have ih_concl : ∀ k : Fin K, c' k = 0 := ih c' const hQ'
      intro k
      by_cases hk : k.val < K
      · have h := ih_concl ⟨k.val, hk⟩
        change c ⟨k.val, _⟩ = 0 at h
        have : k = ⟨k.val, by omega⟩ := Fin.ext rfl
        rw [this]
        exact h
      · have hk_eq : k.val = K := by have := k.isLt; omega
        have : k = kTop := Fin.ext hk_eq
        rw [this]; exact hctop

/-- **General finite Hermite–Pochhammer uniqueness from full
multiplicativity.** If `QFinitePoly K c` satisfies the Cauchy
multiplicative equation, then every coefficient `c_k` vanishes. -/
theorem finite_general_uniqueness
    (K : ℕ) (c : Fin K → ℝ)
    (hmul : ∀ x y : ℝ,
      (QFinitePoly K c).eval (x + y)
        = (QFinitePoly K c).eval x * (QFinitePoly K c).eval y) :
    ∀ k : Fin K, c k = 0 := by
  -- Q(0) ∈ {0, 1} from hmul 0 0.
  have hQ0_dichot :
      (QFinitePoly K c).eval 0 = 1 ∨ (QFinitePoly K c).eval 0 = 0 := by
    have hzz : (QFinitePoly K c).eval 0
        = (QFinitePoly K c).eval 0 * (QFinitePoly K c).eval 0 := by
      have := hmul 0 0
      simpa using this
    have hfac :
        (QFinitePoly K c).eval 0 * ((QFinitePoly K c).eval 0 - 1) = 0 := by
      have := hzz
      ring_nf
      linarith
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
  rcases hQ0_dichot with h0 | h0
  · -- Q(0) = 1 case: translation rigidity at a = 1.
    have htrans : ∀ x : ℝ,
        (QFinitePoly K c).eval (x + 1)
          = (QFinitePoly K c).eval 1 * (QFinitePoly K c).eval x := by
      intro x
      have := hmul x 1
      linarith [mul_comm ((QFinitePoly K c).eval x) ((QFinitePoly K c).eval 1)]
    exact finite_general_uniqueness_of_translation K c 1 one_ne_zero h0 htrans
  · -- Q(0) = 0 case: hmul x 0 forces Q ≡ 0.
    have hzero : ∀ x : ℝ, (QFinitePoly K c).eval x = 0 := by
      intro x
      have := hmul x 0
      rw [add_zero, h0, mul_zero] at this
      exact this
    have hQzero : QFinitePoly K c = 0 := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_zero]
      exact hzero x
    -- Apply the generalized peeling at constant 0.
    have hQC : QFinitePoly K c = Polynomial.C 0 := by
      rw [hQzero]; simp
    exact coeffs_zero_of_QFinitePoly_eq_C K c 0 hQC

end GaussianWhoWhere
