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
The positions of the cops and the robber at a fixed time.
-/
@[ext]
structure CopsRobberPosition (n : ℕ) where
  C : Finset (Fin n)
  R : Fin n

/--
A play of the cops‐and‐robber game on a finite graph. It is given by the
positions of the cops and the robber at each time step, along with the
guarantee that there are no cops at time 0.
-/
structure Play {n : ℕ} (G : SimpleGraph (Fin n)) where
  pos : ℕ → CopsRobberPosition n
  init : (pos 0).C = ∅

@[simp] abbrev Play.C {n : ℕ} {G : SimpleGraph (Fin n)} (play : Play G) :=
  fun t ↦ (play.pos t).C

@[simp] abbrev Play.R {n : ℕ} {G : SimpleGraph (Fin n)} (play : Play G) :=
  fun t ↦ (play.pos t).R

/--
A robber move is valid for a given speed if for every round i there exists a walk
in G from the robber's position at round i to his position at round i+1 such that:
  • The set of vertices (support) visited by the walk, when converted to a finset,
    does not intersect the set of vertices guarded in both rounds i and i+1.
  • The walk's length is at most the allowed speed.
-/
def valid_robber {n : ℕ} {G : SimpleGraph (Fin n)} (play : Play G) (speed : ℕ) : Prop :=
  ∀ t : ℕ,
    ∃ (walk : SimpleGraph.Walk G (play.R t) (play.R (t + 1))),
      (walk.support.toFinset ∩ play.C t ∩ play.C (t + 1) = ∅) ∧
      walk.support.length ≤ (speed+1)

/--
The robber is caught if there is some round t at which the robber's position
is guarded by a cop.
-/
def robber_caught {n : ℕ} {G : SimpleGraph (Fin n)} (play : Play G) : Prop :=
  ∃ t : ℕ, play.R t ∈ play.C t

/--
A cop strategy is a function that, given the current positions of the cops and
the robber, produces the cops' positions for the next round.
-/
abbrev cop_strategy (n : ℕ) : Type := CopsRobberPosition n → Finset (Fin n)

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
    (strat : cop_strategy n) (G : SimpleGraph (Fin n)) (speed : ℕ) (width : ℕ) : Prop :=
  (∀ x, (strat x).card ≤ width)
  ∧ ∀ play : Play G,
    (valid_robber play speed ∧ ∀ i : ℕ, play.C (i + 1) = strat (play.pos i))
      → robber_caught play

/--
The parameter va_cw (for a robber of speed s on a graph G) is defined as the least
number k (i.e. the infimum of such widths) for which there is a cop strategy that
guarantees, against a robber moving legally with speed s, that the robber is eventually
caught while using at most k cops in every round.
-/
noncomputable def va_cw {n : ℕ} (G : SimpleGraph (Fin (n+1))) (s : ℕ) : ℕ :=
  sInf { width : ℕ | ∃ f : cop_strategy (n+1), valid_cop_strategy f G s width }

lemma ex_copstrat {n : ℕ} (G: SimpleGraph (Fin (n+1))) [G.LocallyFinite] (s : ℕ) :
    n + 1 ∈ { width : ℕ | ∃ f : cop_strategy (n+1), valid_cop_strategy f G s width } := by
  simp
  use fun (curr_positions) => Finset.univ
  unfold valid_cop_strategy
  constructor
  · simp [*]
  · unfold robber_caught
    intro play
    intro
    use 1
    simp_all

/--
TODO: Docs
-/
noncomputable def positions_from_hideout
    {n : ℕ} (G : SimpleGraph (Fin (n + 1))) {U : Finset (Fin (n + 1))}
    [G.LocallyFinite] (hU_nonempty : U.Nonempty)
    (strat : cop_strategy (n + 1)) (t : ℕ) :
    CopsRobberPosition (n + 1) :=
match t with
| .zero =>
    ⟨∅, Classical.choose hU_nonempty⟩
| .succ t =>
    let pos := positions_from_hideout G hU_nonempty strat t
    let candidates := (G.neighborFinset pos.R ∩ U) \ strat pos
    ⟨strat pos, if h : candidates.Nonempty then Classical.choose h else pos.R⟩

/--
The possible positions the robber may go to within `U` given a cop strategy
-/
@[simp] noncomputable def positions_from_hideout_candidates
    {n : ℕ} (G : SimpleGraph (Fin (n + 1))) {U : Finset (Fin (n + 1))}
    [G.LocallyFinite] (hU_nonempty : U.Nonempty)
    (strat : cop_strategy (n + 1)) (t : ℕ) :
    Finset (Fin (n + 1)) :=
  let pos := positions_from_hideout G hU_nonempty strat t
  (G.neighborFinset pos.R ∩ U) \ strat pos

/--
Auxillary lemma using `positions_from_hideout_candidates` to make proofs cleaner
-/
lemma positions_from_hideout_eq
    {n : ℕ} (G : SimpleGraph (Fin (n + 1))) {U : Finset (Fin (n + 1))}
    [G.LocallyFinite] (hU_nonempty : U.Nonempty)
    (strat : cop_strategy (n + 1)) (t : ℕ) :
    positions_from_hideout G hU_nonempty strat t = match t with
    | Nat.zero => ⟨∅, Classical.choose hU_nonempty⟩
    | Nat.succ t =>
      let pos := positions_from_hideout G hU_nonempty strat t
      let candidates := positions_from_hideout_candidates G hU_nonempty strat t
      ⟨strat pos, if h : candidates.Nonempty then Classical.choose h else pos.R⟩ := by
  simpa using by rw [positions_from_hideout.eq_def]

lemma positions_from_hideout_robber_in_U
    {n : ℕ} {G : SimpleGraph (Fin (n + 1))} {U : Finset (Fin (n + 1))}
    [G.LocallyFinite] {k : ℕ}
    (hU_nonempty : U.Nonempty)
    (hU : ∀ u ∈ U, (G.neighborFinset u ∩ U).card ≥ k)
    (strat : cop_strategy (n + 1)) (t : ℕ) :
    (positions_from_hideout G hU_nonempty strat t).R ∈ U := by
  rw [positions_from_hideout.eq_def]
  cases t with
  | zero => simpa using Classical.choose_spec hU_nonempty
  | succ t =>
    simp only
    split_ifs with h_candidates
    · apply Finset.mem_of_subset ?_ (Classical.choose_spec h_candidates)
      intro
      simpa using by tauto
    · exact positions_from_hideout_robber_in_U hU_nonempty hU strat t

theorem degeneracy_eq_va_cw_1 {n: ℕ} {G : SimpleGraph (Fin (n+1))} [G.LocallyFinite]: degeneracy G + 1 = va_cw G 1 := by
  let k := degeneracy G
  have k_eq : k=degeneracy G := rfl
  apply Nat.le_antisymm
  · --build robber strat from obstruction
    have : degeneracy G ≥ k := by exact Nat.le_refl (degeneracy G)
    rw [(degeneracy_obstruction G)] at this
    obtain ⟨U, ⟨hU_nonempty, hU⟩⟩ := this
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

    set play : Play G := {
      pos := positions_from_hideout G hU_nonempty strat
      init := by simp [positions_from_hideout]
    } with h_play_eq
    use play
    unfold robber_caught
    simp

    have h_next (t : ℕ) (ht : ¬(positions_from_hideout_candidates G hU_nonempty strat t).Nonempty):
        play.pos (t + 1) = ⟨(G.neighborFinset (play.R t) ∩ U), play.R t⟩ := by
      simp_rw [play]
      rw [positions_from_hideout_eq]
      simp only [ht, dite_false, CopsRobberPosition.ext_iff, and_true]

      simp [positions_from_hideout_candidates] at ht
      apply Finset.eq_of_superset_of_card_ge ht
      calc
        _ ≤ width := strat_width _
        _ ≤ k := valid_strat
        _ ≤ _ := hU _ (positions_from_hideout_robber_in_U ‹_› ‹_› _ _)

    have hRC (t : ℕ) : play.R t ∉ play.C t := by
      cases t with
      | zero => simp [Play.init]
      | succ t =>
        by_cases h_candidates :
            (positions_from_hideout_candidates G hU_nonempty strat t).Nonempty
        · simp only [h_play_eq, Play.R, Play.C]
          rw [positions_from_hideout_eq]
          have := Classical.choose_spec h_candidates
          simp [positions_from_hideout_candidates] at this
          simp only [h_candidates, dite_true, this, not_false_iff]
        · simp [Play.R, Play.C, h_next t h_candidates]

    constructor
    · unfold valid_robber
      rw [← forall_and]
      intro t
      let candidates := positions_from_hideout_candidates G hU_nonempty strat t
      by_cases h : candidates.Nonempty
      · have h_next : play.R (t+1) ∈ candidates := by
          simp only [h_play_eq, Play.R]
          rw [positions_from_hideout_eq]
          simp only [h, candidates, dite_true]
          apply Classical.choose_spec
        have h_adj : G.Adj (play.R t) (play.R (t + 1)) := by
          aesop

        simp
        constructor
        · use h_adj.toWalk
          simp
          have h1 : play.R t ∉ play.C t := hRC t
          have h2 : play.R (t + 1) ∉ play.C (t + 1) := hRC (t + 1)
          aesop
        · simp [play, positions_from_hideout]

      · specialize h_next t h
        constructor
        · rw [show play.R (t + 1) = play.R t by simp [h_next]]
          use SimpleGraph.Walk.nil
          simp [h_next]
        · simp [h_next, play, positions_from_hideout]
    · exact hRC

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
    let f : cop_strategy (n+1) := fun pos ↦ insert pos.R (AdjPred G L pos.R)
    use f
    unfold valid_cop_strategy
    constructor
    · intro pos
      simp [f]
      rw [← k_eq]
      trans (AdjPred G L pos.R).card + 1
      · exact Finset.card_insert_le (pos.R) (AdjPred G L pos.R)
      · simp
        exact h_L pos.R
    · intro play
      intro ⟨h_valid_robber, h_valid_play⟩
      unfold robber_caught
      have h_c : ∀ t, (∃ s ≤ t, play.R s ∈ play.C s) ∨ (L (play.R t)).val ≥ t := by
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
          · have : L (play.R t) < L (play.R (t + 1)) := by
              contrapose! h1
              use (t + 1)
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
                    have : L (play.pos (t + 1)).R = L (play.pos t).R := by
                      exact congrArg (⇑L) (id (Eq.symm h0))
                    aesop
                  · exact h1
                exact SimpleGraph.Walk.adj_of_length_eq_one h
            simp only [Play.R, Play.C] at *
            omega
      specialize h_c (n+1)
      contrapose! h_c
      constructor
      · exact fun s _ ↦ h_c s
      · simp
