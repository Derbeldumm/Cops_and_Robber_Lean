import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic


namespace cops_and_robbers

/-- A layout is represented as a ordering of vertices, so as -/
abbrev Layout (n : ℕ) : Type := Equiv.Perm (Fin n)


def AdjPred {n:ℕ} (G: SimpleGraph (Fin n)) [G.LocallyFinite] (L: Layout n) (v: Fin n) :=
  { w : Fin n | (L w) < (L v) ∧ w ∈ G.neighborFinset v}.toFinset
/-- Count of adjacent predecessors for a vertex v in a given layout -/
def countAdjPred {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (L : Layout n) (v : Fin n) : ℕ :=
  Finset.card (AdjPred G L v)

/-- Verifies if a number k satisfies the degeneracy condition for a given layout -/
def isValidDegeneracy {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] (L : Layout n) (k : ℕ) : Prop :=
  ∀ v : Fin n, countAdjPred G L v ≤ k

/-- The degeneracy (δ*) of a graph is the minimal k over all possible layouts such that
    for each vertex v, there are at most k vertices w ≺ v that are adjacent to v -/
noncomputable def degeneracy {n : ℕ} (G : SimpleGraph (Fin n)) [G.LocallyFinite] : Nat :=
  sInf {n' : ℕ | ∃ L : Layout n, isValidDegeneracy G L n'}


lemma ex_Layout {n : ℕ} (G: SimpleGraph (Fin (n+1))) [G.LocallyFinite]: n ∈ {n_1 | ∃ L, isValidDegeneracy G L n_1} := by
  simp
  let L : Layout (n+1) :=  Equiv.refl (Fin (n+1))
  use L
  unfold isValidDegeneracy
  intro v
  unfold countAdjPred
  unfold AdjPred
  unfold L
  simp
  have subset_eq : {w | w < v ∧ ¬v = w} ⊆ {w | v ≠  w} := by
    intros h hw
    simp
    simp at hw
    exact hw.right

  calc
  _ ≤ {w | w < v ∧ ¬v = w}.toFinset.card := by
    apply Finset.card_le_card
    simp
    apply Finset.subset_iff.mpr
    intro x
    simp
    intro h_lt
    intro
    constructor
    · exact h_lt
    · exact Fin.ne_of_gt h_lt
  _ ≤ {w | v ≠  w}.toFinset.card := by
    simp only [Set.toFinset_card]
    exact Set.card_le_card subset_eq
  _ = n := by
    rw[Set.toFinset_card]
    simp only [ne_eq, Set.coe_setOf, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique, add_tsub_cancel_right]



theorem clique_has_deg_n {n : ℕ} : degeneracy (SimpleGraph.completeGraph (Fin (n+1))) = n := by
  unfold degeneracy
  have nonEmpty := ex_Layout (SimpleGraph.completeGraph (Fin (n+1)))
  apply le_antisymm
  · -- Show degeneracy ≤ n-1
    apply Nat.sInf_le
    exact nonEmpty

  · apply le_csInf
    · exact Set.nonempty_of_mem nonEmpty
    · simp
      intro n'
      intro L
      unfold isValidDegeneracy
      unfold countAdjPred
      unfold AdjPred
      simp
      intro hvalid
      let lastVertex : Fin (n+1) := L.symm (Fin.last (n))
      specialize hvalid lastVertex
      have hlast : ({w | L w < L lastVertex ∧ ¬lastVertex = w} : Finset _) = ({w |¬lastVertex = w} : Finset _) := by
        ext
        unfold lastVertex
        simp
        contrapose!
        intro h
        rw [Fin.last_le_iff] at h
        exact (Equiv.symm_apply_eq L).mpr (id (Eq.symm h))
      apply le_trans _ hvalid
      rw [← ge_iff_le]
      rw [hlast]
      apply ge_of_eq
      trans (Finset.univ.erase lastVertex : Finset (Fin (n + 1))).card
      · congr
        ext
        simp [eq_comm]
      · simp


theorem degeneracy_le_n {n : ℕ} (G: SimpleGraph (Fin (n+1))) [G.LocallyFinite]: degeneracy G ≤ n := by
  unfold degeneracy
  have nonEmpty := ex_Layout G
  apply Nat.sInf_le
  exact nonEmpty


theorem degeneracy_obstruction {n: ℕ} (G : SimpleGraph (Fin (n+1))) [G.LocallyFinite] : ∀ k: ℕ, degeneracy G ≥ k ↔ ∃U : Finset (Fin (n+1)), U.Nonempty ∧ ∀ u ∈ U, (G.neighborFinset u ∩ U).card ≥ k := by
  intro k
  by_cases h_k0 : k=0
  · rw [h_k0]
    simp
    let U : Finset (Fin (n+1)):= {0}
    use U
    unfold U
    simp
  constructor
  · intro h
    contrapose! h
    unfold degeneracy

    have h_induct : ∀ i: Fin (n+1), (∃L : Layout (n+1), ∀a : Fin (n+1), L a > Fin.last n - i → countAdjPred G L a < k) := by
      intro i
      induction i using Fin.induction
      case zero =>
        let L := Equiv.refl (Fin (n+1))
        use L
        intro a
        intro ha
        unfold L at ha
        simp at ha
        contrapose! ha
        exact Fin.le_last a
      case succ i ih =>
        obtain ⟨L, h_L⟩ := ih
        let U := ({a : Fin (n+1) | (L a) ≤ (Fin.last n) - i.castSucc} : Finset (Fin (n + 1)))
        specialize h U
        have U_nempty : U.Nonempty := by
          have : ∃ x, x ∈ U := by
            use (Equiv.symm L) 0
            unfold U
            simp
          exact this
        have h :=  h U_nempty
        obtain ⟨u, Lu⟩ := h
        let newL := (Equiv.swap (L u) ((Fin.last n - i))) * L
        have Lu_le : L u ≤ (Fin.last n - i.castSucc) := by
          unfold U at Lu
          simp at Lu
          exact Lu.1
        have nLu_eq : newL u = Fin.last n - i := by
          unfold newL
          simp
        have id_big : ∀x, newL x > (Fin.last n - i.castSucc) → newL x = L x := by
          intro x
          intro h
          unfold newL
          simp
          refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> (contrapose! h; unfold newL; simp; rw [h]; simp)
          exact Lu_le

        have stab_small : ∀x, newL x ≤ (Fin.last n - i.castSucc) ↔ L x ≤ (Fin.last n - i.castSucc) := by
          intro x
          constructor
          · unfold newL
            by_cases h : L x= L u
            · simp
              rw [h]
              simp
              exact Lu_le
            · by_cases h_eq : L x = Fin.last n - i.castSucc
              · rw [h_eq]
                simp
              · simp
                have : (Equiv.swap (L u) (Fin.last n - i.castSucc)) (L x) = L x := by
                  apply Equiv.swap_apply_of_ne_of_ne
                  · exact h
                  · exact h_eq
                rw [this]
                simp
          · unfold newL
            by_cases h_eq : L x= L u
            · simp
              rw [h_eq]
              simp
            · by_cases h : L x = Fin.last n - i.castSucc
              · simp
                rw [h]
                simp
                exact Lu_le
              · simp
                have : (Equiv.swap (L u) (Fin.last n - i.castSucc)) (L x) = L x := by
                  apply Equiv.swap_apply_of_ne_of_ne
                  · exact h_eq
                  · exact h
                rw [this]
                simp
        use newL
        intro a
        intro ha
        by_cases h : (newL a) ≤ ((Fin.last n - i.castSucc) : Fin (n+1))
        · unfold countAdjPred
          calc
          _ ≤ (G.neighborFinset a ∩ U).card := by
            apply Finset.card_le_card
            apply Finset.subset_iff.mpr
            intro x
            unfold AdjPred
            simp
            intro newL_lt
            intro adj
            constructor
            · exact adj
            · unfold U
              simp
              rw [← stab_small]
              trans newL a
              · exact Fin.le_of_lt newL_lt
              · exact h
          _ < k := by
            have La_eq_Lu : newL a= newL u:= by
              trans Fin.last n - i.castSucc
              · apply le_antisymm
                · exact h
                · rw [← ge_iff_le]
                  trans Fin.last n - i.succ + 1
                  · exact Fin.add_one_le_of_lt ha
                  · apply le_of_eq
                    refine Fin.eq_of_val_eq ?_
                    rw [@Fin.val_add_one]
                    simp
                    simp [Fin.last_sub]
                    omega
                    -- rw [← Nat.sub_sub, Nat.sub_one, Nat.add_one]
                    -- symm
                    -- refine Nat.succ_pred ?_
                    -- apply ne_of_gt
                    -- refine Nat.sub_pos_of_lt ?_
                    -- exact i.isLt
              · rw [nLu_eq]
                simp
            have a_eq_u : a=u:= by
              refine newL.injective La_eq_Lu
            rw [a_eq_u]
            exact Lu.2
        · apply not_le.mp at h
          rw [← gt_iff_lt] at h
          have h' := h
          have h'' := h
          apply id_big at h
          rw [h] at h'
          apply h_L at h'
          unfold countAdjPred
          calc
          _ ≤ (AdjPred G L a).card := by
            apply Finset.card_le_card
            refine Finset.subset_iff.mpr ?_
            intro x
            unfold AdjPred
            simp
            intro h1
            intro h2
            constructor
            · rw [h] at h1
              by_cases h3: (newL x) ≤ (Fin.last n - i.castSucc)
              · calc
                _ ≤ Fin.last n - i.castSucc := by
                  rw [stab_small] at h3
                  exact h3
                _ < L a := by
                  rw [← h]
                  exact h''
              · simp at h3
                apply id_big at h3
                rw [← h3]
                exact h1
            · exact h2
          _ < k := by
            exact h'

    specialize h_induct (Fin.last (n))
    obtain ⟨L, h_L⟩ := h_induct
    have h2 : k-1 ∈ {n' | ∃ L, isValidDegeneracy G L n'} := by
      simp
      use L
      unfold isValidDegeneracy
      intro v
      specialize h_L v
      simp at h_L
      by_cases h : L v > 0
      · apply h_L at h
        exact Nat.le_sub_one_of_lt h
      · simp at h
        trans 0
        · unfold countAdjPred
          unfold AdjPred
          simp
          rw [h]
          simp
        · simp

    apply Nat.lt_of_le_pred
    · apply lt_of_le_of_ne
      exact Nat.zero_le k
      exact fun a ↦ h_k0 (id (Eq.symm a))
    · simp
      exact Nat.sInf_le h2
  · intro h
    obtain ⟨U, hU_nonempty, hU_count⟩ := h
    rw [degeneracy]
    apply le_csInf
    · exact Set.nonempty_of_mem (ex_Layout G)
    · intro b
      intro hb
      simp at hb
      unfold isValidDegeneracy at hb
      obtain ⟨L, HL⟩ := hb

      obtain ⟨u, hu_mem, hu_eq⟩ := Finset.exists_mem_eq_sup' hU_nonempty L

      have u_max : ∀ v ∈ U, v ≠ u → L v < L u := by
        intro v
        intro v_in_U
        intro v_ne_u
        apply lt_of_le_of_ne
        · rw [← hu_eq]
          exact Finset.le_sup' _ v_in_U
        · exact (Equiv.apply_eq_iff_eq L).not.mpr v_ne_u
      specialize hU_count u
      have hU_count := hU_count hu_mem
      specialize HL u
      unfold countAdjPred at HL
      calc
      _ ≤ (G.neighborFinset u ∩ U).card := hU_count
      _ ≤ (AdjPred G L u).card := by
        apply Finset.card_le_card
        apply Finset.subset_iff.mpr
        intro x
        simp
        intro adj_ux
        intro x_in_u
        unfold AdjPred
        simp
        constructor
        · specialize u_max x
          have u_max := u_max x_in_u
          have x_ne_u : x≠u := by
            contrapose! adj_ux
            rw [adj_ux]
            exact SimpleGraph.irrefl G
          have u_max := u_max x_ne_u
          exact u_max
        · exact adj_ux
      _ ≤ b := HL

/--
A play of the cops‐and‐robber game on a finite graph.
• S : ℕ → Finset (Fin n) gives the cops' positions (as a finset)
  in each round (with S 0 = ∅).
• R : ℕ → Fin n gives the robber's position in each round.
-/
structure Play {n : ℕ} (G : SimpleGraph (Fin n)) where
  (C : ℕ → Finset (Fin n))
  (R : ℕ → Fin n)
  (init : C 0 = ∅)

/--
A robber move is valid for a given speed if for every round i there exists a walk
in G from the robber's position at round i to his position at round i+1 such that:
  • The set of vertices (support) visited by the walk, when converted to a finset,
    does not intersect the set of vertices guarded in both rounds i and i+1.
  • The walk's length is at most the allowed speed.
-/
def valid_robber {n : ℕ} {G : SimpleGraph (Fin n)} (play : Play G) (speed : ℕ) : Prop :=
  ∀ t : ℕ,
    ∃ (walk : SimpleGraph.Walk G (play.R t) (play.R (t+1))),
      (walk.support.toFinset ∩ (play.C t) ∩ (play.C (t+1)) = ∅) ∧
      walk.support.length ≤ (speed+1)

/--
The robber is caught if there is some round t at which the robber's position
is guarded by a cop.
-/
def robber_caught {n : ℕ} {G : SimpleGraph (Fin n)} (p : Play G) : Prop :=
  ∃ t : ℕ, p.R t ∈ p.C t


/--
A cop strategy is a function that, given the current positions of the cops and
the robber, produces the cops' positions for the next round.
-/
abbrev cop_strategy (n : ℕ) : Type :=
  (curr_positions: Finset (Fin n) × (Fin n)) → Finset (Fin n)

/--
A cop strategy is valid (with parameters speed and width) if for every play on G
that meets the following:
  - The robber always moves legally (with speed `speed`).
  - The cops' positions are updated according to the strategy.
it follows that:
  - The robber is eventually caught.
  - The number of cops used at every round does not exceed `width`.
-/
def valid_cop_strategy {n : ℕ}
  (strat : cop_strategy n) (G : SimpleGraph (Fin n)) (speed : ℕ) (width : ℕ): Prop :=
  (∀x:(Finset (Fin n) × (Fin n)), (strat x).card ≤ width
  )∧
  (∀ play : Play G,
    ((valid_robber play speed) ∧ (∀ i : ℕ, play.C (i+1) = strat (play.C i, play.R i))) → robber_caught play)

/--
The parameter va_cw (for a robber of speed s on a graph G) is defined as the least
number k (i.e. the infimum of such widths) for which there is a cop strategy that
guarantees, against a robber moving legally with speed s, that the robber is eventually
caught while using at most k cops in every round.
-/
noncomputable def va_cw {n : ℕ} (G : SimpleGraph (Fin (n+1))) (s : ℕ) : ℕ :=
  sInf { width : ℕ | ∃ f : cop_strategy (n+1), valid_cop_strategy f G s width }


lemma ex_copstrat {n : ℕ} (G: SimpleGraph (Fin (n+1))) [G.LocallyFinite] (s:ℕ): n+1 ∈ { width : ℕ | ∃ f : cop_strategy (n+1), valid_cop_strategy f G s width } := by
  simp
  let f : cop_strategy (n+1) := fun (curr_positions) => Finset.univ
  use f
  unfold valid_cop_strategy
  constructor
  · simp [*]
    aesop
  · unfold robber_caught
    intro play
    intro
    use 1
    simp_all
    aesop

noncomputable def positions_from_hideout
    {n : ℕ} {G : SimpleGraph (Fin (n + 1))} {U : Finset (Fin (n + 1))}
    [G.LocallyFinite] {k : ℕ}
    (h_U : U.Nonempty ∧ ∀ u ∈ U, (G.neighborFinset u ∩ U).card ≥ k)
    (strat : cop_strategy (n + 1))
    (t : ℕ) : (Finset (Fin (n+1)) × U) := match t with
| .zero =>
    let u₀ := Classical.choose h_U.left
    let h₀ : u₀ ∈ U := Classical.choose_spec h_U.left
    (∅, ⟨u₀, h₀⟩)
| .succ t =>
    let candidates := (G.neighborFinset (positions_from_hideout h_U strat t).2 ∩ U) \ strat
      ((positions_from_hideout h_U strat t).1, (positions_from_hideout h_U strat t).2)
    if h : candidates.Nonempty then
      let r := Classical.choose h
      have hr : r ∈ candidates := Classical.choose_spec h
      have : r ∈ U := by
        simp [candidates] at hr
        exact hr.1.2
      (strat ((positions_from_hideout h_U strat t).1, (positions_from_hideout h_U strat t).2),⟨r,this⟩)
    else
      (strat ((positions_from_hideout h_U strat t).1, (positions_from_hideout h_U strat t).2),(positions_from_hideout h_U strat t).2)

noncomputable section
 theorem degeneracy_eq_va_cw_1 {n: ℕ} {G : SimpleGraph (Fin (n+1))} [G.LocallyFinite]: degeneracy G + 1 = va_cw G 1 := by
  let k := degeneracy G
  have k_eq : k=degeneracy G := rfl
  apply Nat.le_antisymm
  · --build robber strat from obstruction
    have : degeneracy G ≥ k := by exact Nat.le_refl (degeneracy G)
    rw [(degeneracy_obstruction G)] at this
    obtain ⟨U, h_U⟩ := this
    rw [← k_eq]
    unfold va_cw
    apply le_csInf
    exact Set.nonempty_of_mem (ex_copstrat G 1)
    intro width
    simp
    intro strat
    intro valid_strat
    unfold valid_cop_strategy at valid_strat
    contrapose! valid_strat
    intro strat_width
    apply Nat.le_of_lt_add_one at valid_strat

    let positions' := positions_from_hideout h_U strat

    -- let u : Fin (n+1) =
    let play : Play G := {
      C := fun t => (positions' t).1,
      R := fun t => (positions' t).2.1,
      init := by simp [positions', positions_from_hideout]
    }
    use play
    unfold robber_caught
    simp
    constructor
    · unfold valid_robber
      rw [← forall_and]
      intro t
      let candidates := (G.neighborFinset (positions' t).2 ∩ U) \ strat ((positions' t).1, (positions' t).2.1)
      by_cases h : candidates.Nonempty
      · have h_next : (positions' (t+1)).2.1 ∈ candidates := by
          simp_rw [positions']
          rw [positions_from_hideout]
          simp only [positions', h, candidates]
          simp only [↓reduceDIte]
          apply Classical.choose_spec
        simp

        have h_adj : G.Adj ↑(positions' t).2 ↑(positions' (t + 1)).2 := by
          aesop
        constructor
        · use SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil
          simp
          have h1 : play.R t ∉ play.C t := sorry
          have h2 : ↑(positions' (t + 1)).2 ∉ play.C (t+1) := sorry
          aesop
        · simp [play]
          simp_rw [positions']
          rw [positions_from_hideout]
          simp only [positions', h, candidates]
          simp

      · have h_next : positions' (t+1) = ((G.neighborFinset (positions' t).2 ∩ U),(positions' t).2) := by
          simp_rw [positions']
          rw [positions_from_hideout]
          simp [positions', h, candidates]

          let S_strat := strat ((positions_from_hideout h_U strat t).1, ↑((positions_from_hideout h_U strat t).2))
          let S_neighbors := G.neighborFinset ↑((positions_from_hideout h_U strat t).2) ∩ U

          apply Eq.symm
          apply Finset.eq_of_subset_of_card_le
          · have h_empty : S_neighbors \ S_strat = ∅ := by
              exact Finset.not_nonempty_iff_eq_empty.mp h
            exact Finset.sdiff_eq_empty_iff_subset.mp h_empty
          · have card_strat_le_k : S_strat.card ≤ k :=
              (strat_width _).trans valid_strat

            have robber_in_U : ↑((positions_from_hideout h_U strat t).2) ∈ U :=
              (positions_from_hideout h_U strat t).2.property
            have card_neighbors_ge_k : S_neighbors.card ≥ k :=
              h_U.2 _ robber_in_U

            -- Combining the two inequalities proves the goal.
            exact card_strat_le_k.trans card_neighbors_ge_k
        have h_eq : play.R (t+1) = play.R (t) := by
          calc
          _ = (positions' (t+1)).2.1 := rfl
          _ = (positions' t).2.1 := by simp_all
          _ = play.R (t) := by rfl
        rw [h_eq]
        constructor
        · use SimpleGraph.Walk.nil
          simp
          refine Finset.singleton_inter_of_not_mem ?_
          simp
          intro
          have h_cops : play.C (t + 1) = (G.neighborFinset (play.R t) ∩ U) := by
            calc
            _ = (positions' (t+1)).1 := rfl
            _ = (G.neighborFinset (positions' t).2 ∩ U) := by simp_all
            _ = (G.neighborFinset (play.R t) ∩ U) := by congr
          rw [h_cops]
          simp
        · simp [play]
          simp_rw [positions']
          rw [positions_from_hideout]
          simp only [positions', h, candidates]
          simp
    · sorry


  · --build cop strat from Layout
    have : k ∈ ({n' | ∃ L, isValidDegeneracy G L n'}) := by
      unfold k; unfold degeneracy
      apply Nat.sInf_mem
      exact Set.nonempty_of_mem (ex_Layout G)
    simp at this

    obtain ⟨L, h_L⟩ := this
    unfold va_cw
    apply Nat.sInf_le
    simp
    let f : cop_strategy (n+1) := fun (curr_positions) =>
      insert curr_positions.snd (AdjPred G L curr_positions.snd)
    use f
    unfold valid_cop_strategy
    constructor
    · intro positions
      simp [f]
      rw [← k_eq]
      trans (AdjPred G L (positions.2)).card + 1
      · exact Finset.card_insert_le (positions.2) (AdjPred G L (positions.2))
      · simp
        exact h_L (positions.2)
    · intro play
      intro ⟨h_valid_robber, h_valid_play⟩
      unfold robber_caught
      have h_c : ∀t, (∃s≤t, play.R s ∈ play.C s) ∨ (L (play.R t)).val ≥ t := by
        intro t
        induction t
        case zero =>
          simp
        case succ t h_ind =>
          contrapose h_ind
          simp_all
          obtain ⟨h1,h2⟩ := h_ind
          constructor
          · intro x
            specialize h1 x
            intro h
            have : x ≤ t+1 := by
              exact Nat.le_add_right_of_le h
            apply h1 at this
            exact this
          · have : (L (play.R t)) < (L (play.R (t + 1))) := by
              contrapose! h1
              use (t+1)
              simp
              simp [*]
              simp [f]
              apply Fin.eq_or_lt_of_le at h1
              rcases h1 with inl | inr
              · left
                aesop
              · right
                unfold AdjPred
                simp_all
                unfold valid_robber at h_valid_robber
                specialize h_valid_robber t
                obtain ⟨walk,⟨_,h_walk⟩⟩ := h_valid_robber
                simp at h_walk
                have h : walk.length = 1 := by
                  cases' Nat.le_one_iff_eq_zero_or_eq_one.mp h_walk with h0 h1
                  · apply SimpleGraph.Walk.eq_of_length_eq_zero at h0
                    have : L (play.R (t + 1)) = L (play.R t) := by
                      exact congrArg (⇑L) (id (Eq.symm h0))
                    aesop
                  · exact h1
                exact SimpleGraph.Walk.adj_of_length_eq_one h
            omega
      specialize h_c (n+1)
      contrapose! h_c
      constructor
      · exact fun s _ ↦ h_c s
      · simp
