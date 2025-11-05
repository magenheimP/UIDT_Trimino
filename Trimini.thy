theory Trimini
  imports Main
begin
(*declare [[show_types]] *)


datatype Orientation = NW | NE | SW | SE
datatype Kvadrant = I | II | III | IV

type_synonym Tromino = "int * int * Orientation"
type_synonym Rupa = "int * int"

fun pow2 :: "int \<Rightarrow> int" where
  "pow2 n = 2 ^ nat n"

fun translate_one :: "(int * int) \<Rightarrow> Tromino \<Rightarrow> Tromino" where
  "translate_one (dx, dy) (x, y, orient) = (x + dx, y + dy, orient)"

fun translate :: "(int * int) \<Rightarrow> Tromino list \<Rightarrow> Tromino list" where
  "translate delta ts = map (translate_one delta) ts"

fun base_case :: "Rupa \<Rightarrow> Tromino list" where
  "base_case r = (case r of
      (x, y) \<Rightarrow>
        (if x = 0 \<and> y = 0 then [(1, 1, SE)]
         else if x = 0 \<and> y = 1 then [(1, 0, NE)]
         else if x = 1 \<and> y = 0 then [(0, 1, SW)]
         else [(0, 0, NW)]))"

fun where_is_the_whole :: "int \<Rightarrow> Rupa \<Rightarrow> Kvadrant" where
  "where_is_the_whole s (x,y) =
     (let half = s div 2 in
      if x < half \<and> y < half then I
      else if x < half \<and> y \<ge> half then II
      else if x \<ge> half \<and> y \<ge> half then III
      else IV)"

fun center :: "int \<Rightarrow> Rupa \<Rightarrow> Tromino list" where
  "center s rupa =
     (if s = 2 then base_case rupa
      else
        (let half = s div 2 in
         case where_is_the_whole s rupa of
           I \<Rightarrow> [(half, half, SE)] |
           II \<Rightarrow> [(half, half - 1, NE)] |
           III \<Rightarrow> [(half - 1, half - 1, NW)] |
           IV \<Rightarrow> [(half - 1, half, SW)]))"

fun nove_rupe :: "int \<Rightarrow> Rupa \<Rightarrow> Rupa list" where
  "nove_rupe s rupa =
     (case hd (center s rupa) of
        (x, y, NW) \<Rightarrow> [(x, y), (x, y + 1), rupa, (x + 1, y)] |
        (x, y, NE) \<Rightarrow> [(x - 1, y), rupa, (x, y + 1), (x, y)] |
        (x, y, SW) \<Rightarrow> [(x, y - 1), (x, y), (x + 1, y), rupa] |
        (x, y, SE) \<Rightarrow> [rupa, (x - 1, y), (x, y), (x, y - 1)])"

fun rekurzija_rupe :: "int \<Rightarrow> Rupa list \<Rightarrow> Rupa list" where
  "rekurzija_rupe s [(x1,y1), (x2,y2), (x3,y3), (x4,y4)] =
      [(x1,y1),
       (x2, y2 - s div 2),
       (x3 - s div 2, y3 - s div 2),
       (x4 - s div 2, y4)]" |
  "rekurzija_rupe _ _ =  [] " (* ovo sam dodao jer mi se bunio da nema patern za neke slucaje*)


fun tile :: "int \<Rightarrow> Rupa \<Rightarrow> Tromino list" where
  "tile n rupa =
     (if n \<le> 0 then []
      else if n = 1 then base_case rupa
      else
        (let size = pow2 n;
             center_tromino = center size rupa;
             holes = nove_rupe size rupa;
             rec_hole = rekurzija_rupe size holes;
             prvi = tile (n - 1) (rec_hole ! 0);
             drugi = translate (0, size div 2) (tile (n - 1) (rec_hole ! 1));
             treci = translate (size div 2, size div 2) (tile (n - 1) (rec_hole ! 2));
             cetvrti = translate (size div 2, 0) (tile (n - 1) (rec_hole ! 3))
         in center_tromino @ prvi @ drugi @ treci @ cetvrti))"



value "tile 3 (3,5)"










end

