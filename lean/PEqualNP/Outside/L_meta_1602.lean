import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1602

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_pre (gs : List Gate) (acc : List Bool) :
    ∃ t, gs.foldl stp acc = acc ++ t ∧
      (gs.foldl stp acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (stp acc g)
    refine ⟨[g.op.eval (g.inputs.map fun i => acc.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [stp]
    · rw [List.foldl_cons, hl]
      simp only [stp, List.length_append, List.length_cons, List.length_nil]
      omega

lemma getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < m then x ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_default]; simp; omega

def Ind {m : ℕ} (H : SimpleGraph (Fin m)) (x : Fin m → Bool) : Prop :=
  ∀ u v, H.Adj u v → ¬ (x u = true ∧ x v = true)

lemma ind_pair {m : ℕ} (H : SimpleGraph (Fin m)) (a b : Fin m) (h : ¬ H.Adj a b) :
    Ind H (PEqualNP.EdgeOwnership.pairInput a b) := by
  intro u v huv ⟨hu, hv⟩
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact huv.ne rfl
  · exact h huv
  · exact h huv.symm
  · exact huv.ne rfl

lemma pair_left {m : ℕ} (a b : Fin m) : PEqualNP.EdgeOwnership.pairInput a b a = true := by
  simp [PEqualNP.EdgeOwnership.pairInput]

lemma pair_right {m : ℕ} (a b : Fin m) : PEqualNP.EdgeOwnership.pairInput a b b = true := by
  simp [PEqualNP.EdgeOwnership.pairInput]

def W (m : ℕ) (gs : List Gate) (k : ℕ) (x : Fin m → Bool) : List Bool :=
  (gs.take k).foldl stp (List.ofFn x)

def Inv {m : ℕ} (H : SimpleGraph (Fin m)) (V : (Fin m → Bool) → List Bool) : Prop :=
  ∀ i x, Ind H x → ((V x).getD i false = true ↔
    ∃ v, x v = true ∧ (V (PEqualNP.EdgeOwnership.pairInput v v)).getD i false = true)

lemma W_len (m : ℕ) (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) (x : Fin m → Bool) :
    (W m gs k x).length = m + k := by
  obtain ⟨t, -, hl⟩ := foldl_pre (gs.take k) (List.ofFn x)
  unfold W; rw [hl]; simp; omega

lemma W_succ (m : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Fin m → Bool) :
    W m gs (k+1) x = stp (W m gs k x) gs[k] := by
  unfold W; rw [List.take_succ_eq_append_getElem hk, List.foldl_append]; rfl

lemma W_final (m : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin m → Bool) :
    (C.wires (List.ofFn x)).getD (m + k) false = (W m C.gates (k+1) x).getD (m + k) false := by
  have h1 : C.wires (List.ofFn x) = (C.gates.drop (k+1)).foldl stp (W m C.gates (k+1) x) := by
    unfold W; rw [← List.foldl_append, List.take_append_drop]; rfl
  obtain ⟨t, ht, -⟩ := foldl_pre (C.gates.drop (k+1)) (W m C.gates (k+1) x)
  rw [h1, ht]
  apply List.getD_append
  rw [W_len m C.gates (k+1) hk x]; omega

lemma inv_all {m : ℕ} (hm : 0 < m) (H : SimpleGraph (Fin m)) (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hand : ∀ k (hk : k < gs.length), gs[k].op = GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w →
       (W m gs (k+1) (PEqualNP.EdgeOwnership.pairInput e w)).getD (m + k) false = false) :
    ∀ k, k ≤ gs.length → Inv H (W m gs k) := by
  intro k
  induction k with
  | zero =>
    intro _ i x _
    simp only [W, List.take_zero, List.foldl_nil, getD_ofFn]
    split_ifs with h
    · constructor
      · intro hx; exact ⟨⟨i, h⟩, hx, pair_left _ _⟩
      · rintro ⟨v, hv, h2⟩
        have : (⟨i, h⟩ : Fin m) = v := by
          simpa [PEqualNP.EdgeOwnership.pairInput] using h2
        rw [this]; exact hv
    · simp
  | succ k ih =>
    intro hk
    have hk' : k < gs.length := by omega
    have IH := ih (by omega)
    have hA : ∀ e w : Fin m, gs[k].op = GateOp.and → ¬ H.Adj e w →
        gs[k].op.eval (gs[k].inputs.map fun j =>
          (W m gs k (PEqualNP.EdgeOwnership.pairInput e w)).getD j false) = false := by
      intro e w hop hew
      have := hand k hk' hop e w hew
      rw [W_succ m gs k hk', stp, getD_snoc, W_len m gs k (by omega)] at this
      simpa using this
    intro i x hx
    simp only [W_succ m gs k hk', stp, getD_snoc, W_len m gs k (by omega)]
    split_ifs with h1 h2
    · exact IH i x hx
    · obtain ⟨hop, hlen⟩ := hmono gs[k] (List.getElem_mem hk')
      rcases hop with hop | hop
      · constructor
        · intro hval
          exfalso
          rw [hop] at hval
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply,
            id_eq] at hval
          rcases hinp : gs[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · have := hA ⟨0, hm⟩ ⟨0, hm⟩ hop (fun h => h.ne rfl)
            rw [hop, hinp] at this
            simp [GateOp.eval] at this
          · obtain ⟨v, hv1, hv2⟩ := (IH a x hx).1 (hval a (by simp [hinp]))
            have := hA v v hop (fun h => h.ne rfl)
            rw [hop, hinp] at this
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.true_and, Bool.true_eq_false, hv2] at this
          · obtain ⟨va, hva1, hva2⟩ := (IH a x hx).1 (hval a (by simp [hinp]))
            obtain ⟨vb, hvb1, hvb2⟩ := (IH b x hx).1 (hval b (by simp [hinp]))
            have hab : ¬ H.Adj va vb := fun hadj => hx va vb hadj ⟨hva1, hvb1⟩
            have hI := ind_pair H va vb hab
            have ha := (IH a _ hI).2 ⟨va, pair_left _ _, hva2⟩
            have hb := (IH b _ hI).2 ⟨vb, pair_right _ _, hvb2⟩
            have := hA va vb hop hab
            rw [hop, hinp] at this
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.true_and, Bool.true_eq_false, ha, hb] at this
          · rw [hinp] at hlen; simp at hlen
        · rintro ⟨v, -, hv⟩
          rw [hA v v hop (fun h => h.ne rfl)] at hv
          exact absurd hv (by simp)
      · rw [hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        constructor
        · rintro ⟨j, hj, hv⟩
          obtain ⟨v, hv1, hv2⟩ := (IH j x hx).1 hv
          exact ⟨v, hv1, j, hj, hv2⟩
        · rintro ⟨v, hv1, j, hj, hv2⟩
          exact ⟨j, hj, (IH j x hx).2 ⟨v, hv1, hv2⟩⟩
    · simp

end PEqualNP.Outside.L_meta_1602

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hyp m H _ hH D hD hfun hAnd
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have : H.edgeFinset = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ a _ => exact a.elim0
    simp [this]
  · have hmono : ∀ g ∈ D.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have := hD g hg
      simpa using this
    have hand' : ∀ k (hk : k < D.gates.length), D.gates[k].op = GateOp.and →
        ∀ e w : Fin m, ¬ H.Adj e w →
        (PEqualNP.Outside.L_meta_1602.W m D.gates (k+1)
          (PEqualNP.EdgeOwnership.pairInput e w)).getD (m + k) false = false := by
      intro k hk hop e w hew
      rw [← PEqualNP.Outside.L_meta_1602.W_final m D k hk]
      have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = GateOp.and := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
          using hop
      exact hAnd k hk hop' e w hew
    have hinv := PEqualNP.Outside.L_meta_1602.inv_all hm H D.gates hmono hand'
    refine hyp m H hH D.gates D.output hmono ?_ ?_
    · intro x
      have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · intro i x hop hw
      by_contra hne
      have hx : PEqualNP.Outside.L_meta_1602.Ind H x := fun u v huv h => hne ⟨u, v, huv, h⟩
      have h1 := PEqualNP.Outside.L_meta_1602.W_final m ⟨D.gates, 0⟩ i i.2 x
      rw [h1] at hw
      obtain ⟨v, -, hv⟩ := (hinv (i+1) i.2 (m + i) x hx).1 hw
      have hop2 : D.gates[(i : ℕ)].op = GateOp.and := by simpa using hop
      rw [hand' i i.2 hop2 v v (fun h => h.ne rfl)] at hv
      exact absurd hv (by simp)
