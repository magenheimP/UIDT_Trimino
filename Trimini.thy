theory Trimini
  imports Main
begin
(*declare [[show_types]] *)
(*
Tvrdjenje koje bi moglo da se dokaze je da za svaku tablu dimenzija 2^n x 2^n
kojoj nedostaje jedno polje postoji ispravno trimini poplocavanje

*)


datatype Orientation = NW | NE | SW | SE
datatype Kvadrant = I | II | III | IV

(*Trimini posmatramo kao strelice koje su usmerene prema
stranama sveta, koordina su koodinate spica strelice *)
type_synonym Tromino = "nat * nat * Orientation"
type_synonym Rupa = "nat * nat"

fun pow2 :: "nat ⇒ nat" where
  "pow2 n = 2 ^ n"

fun translate_one :: "(nat * nat) ⇒ Tromino ⇒ Tromino" where
  "translate_one (dx, dy) (x, y, orient) = (x + dx, y + dy, orient)"

fun translate :: "(nat * nat) ⇒ Tromino list ⇒ Tromino list" where
  "translate delta ts = map (translate_one delta) ts"

fun base_case :: "Rupa ⇒ Tromino list" where
  "base_case (0,0) = [(1, 1, SE)]" |
  "base_case (0,Suc 0) = [(1, 0, NE)]" |
  "base_case (Suc 0,0) = [(0, 1, SW)]" |
  "base_case (Suc 0,Suc 0) = [(0, 0, NW)]"



fun where_is_the_whole :: "nat ⇒ Rupa ⇒ Kvadrant" where
  "where_is_the_whole s (x,y) =
     (let half = s div 2 in
      if x < half ∧ y < half then I
      else if x < half ∧ y ≥ half then II
      else if x ≥ half ∧ y ≥ half then III
      else IV)"

fun center :: "nat ⇒ Rupa ⇒ Tromino list" where
  "center s rupa =
     (if s = 2 then base_case rupa
      else
        (let half = s div 2 in
         case where_is_the_whole s rupa of
           I ⇒ [(half, half, SE)] |
           II ⇒ [(half, half - 1, NE)] |
           III ⇒ [(half - 1, half - 1, NW)] |
           IV ⇒ [(half - 1, half, SW)]))"

fun nove_rupe :: "nat ⇒ Rupa ⇒ Rupa list" where
  "nove_rupe s rupa =
     (case hd (center s rupa) of
        (x, y, NW) ⇒ [(x, y), (x, y + 1), rupa, (x + 1, y)] |
        (x, y, NE) ⇒ [(x - 1, y), rupa, (x, y + 1), (x, y)] |
        (x, y, SW) ⇒ [(x, y - 1), (x, y), (x + 1, y), rupa] |
        (x, y, SE) ⇒ [rupa, (x - 1, y), (x, y), (x, y - 1)])"

fun rekurzija_rupe :: "nat ⇒ Rupa list ⇒ Rupa list" where
  "rekurzija_rupe s [(x1,y1), (x2,y2), (x3,y3), (x4,y4)] =
      [(x1,y1),
       (x2, y2 - s div 2),
       (x3 - s div 2, y3 - s div 2),
       (x4 - s div 2, y4)]" |
  "rekurzija_rupe _ _ =  [] " (* ovo sam dodao jer mi se bunio da nema patern za neke slucaje*)


fun tile :: "nat ⇒ Rupa ⇒ Tromino list" where
  "tile 0 rupa = []" |
  "tile (Suc 0) rupa = base_case rupa" |
  "tile n rupa =
    (let size = pow2 n;
         center_tromino = center size rupa;
         holes = nove_rupe size rupa;
         rec_hole = rekurzija_rupe size holes;
         prvi = tile (n - 1) (rec_hole ! 0);
         drugi = translate (0, size div 2) (tile (n - 1) (rec_hole ! 1));
         treci = translate (size div 2, size div 2) (tile (n - 1) (rec_hole ! 2));
         cetvrti = translate (size div 2, 0) (tile (n - 1) (rec_hole ! 3))
     in center_tromino @ prvi @ drugi @ treci @ cetvrti)"


value "tile 3 (3,5)" (*Ovo je primer iz aisp skripte*)

fun board_cells :: "nat ⇒ (nat × nat) set" where
  "board_cells n = {(i, j). i < pow2 n ∧ j < pow2 n}"


fun cells_of_tromino :: "Tromino ⇒ (nat × nat) set" where
  "cells_of_tromino (x, y, NW) = {(x, y), (x+1, y), (x, y+1)}" |
  "cells_of_tromino (x, y, NE) = {(x, y), (x-1, y), (x, y+1)}" |
  "cells_of_tromino (x, y, SW) = {(x, y), (x, y-1), (x+1, y)}" |
  "cells_of_tromino (x, y, SE) = {(x, y), (x-1, y), (x, y-1)}"


fun valid_tromino :: "nat ⇒ Tromino ⇒ bool" where
  "valid_tromino n t ⟷ cells_of_tromino t ⊆ board_cells n"

fun valid_tiling :: "nat ⇒ Tromino list ⇒ bool" where
  "valid_tiling n ts ⟷ (∀t ∈ set ts. valid_tromino n t) ∧
   (∀ x  ∈ set ts. ∀y ∈ set ts. x≠y ⟶  cells_of_tromino x ∩ cells_of_tromino y = {})"

fun valid_hole :: "nat ⇒ Rupa ⇒ bool" where
  "valid_hole n (x, y) ⟷ ( x < pow2 n ∧ y < pow2 n)"

lemma "valid_hole 1 (0,0)"
  by simp
lemma "valid_hole 1 (1,0)"
  by simp
lemma "valid_hole 1 (1,1)"
  by simp
lemma "valid_hole 1 (0,1)"
  by simp
lemma nevalidne_rupe:
" x > 1 ∨  y > 1  ⟹ ¬valid_hole 1 (x,y)"
  by auto


value "valid_hole 3 (3,5)"    (* True *)
value "valid_hole 2 (4,0)"    (* False — x = 8 je van granica *)
value "valid_hole 4 (24,1)"   (* False — negativna koordinata *)


(* 
Za svako n i  svaku tablu dimenzija 2^n x 2^n i bilo koju ispravnu rupu postoji
validno trimini poplocavanje
*)

lemma 
  assumes "valid_hole n h"
  shows "valid_tiling n (tile n h)"
  using assms
proof (induction n h rule: tile.induct)
  case (1 rupa)
  then show ?case by auto
next
  case (2 rupa)
  then show ?case
  proof (cases "rupa = (0,0)")
    case True
    from True show ?thesis by simp
  next
    case False
    then show ?thesis
    proof(cases "rupa = (1,0)")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "rupa = (0,1)")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
        proof (cases "rupa = (1,1)")
          case True
          then show ?thesis by simp
        next
          case False
          with ‹rupa ≠ (0,1)› ‹rupa ≠ (0,0)› ‹rupa ≠ (1,0)› show ?thesis using nevalidne_rupe
            by (metis "2" One_nat_def less_Suc0 nat_neq_iff valid_hole.elims(2))
        qed
      qed
    qed
  qed
next
  case (3 va rupa)
  then show ?case sorry
qed













lemma pow2_positive:
  shows "pow2 n > 0"
  by induction auto

lemma translate_preserves_length:
  "length (translate d ts) = length ts"
  by auto


lemma center_length_1:
  "length (center s hole) = 1"
  sorry



















end

