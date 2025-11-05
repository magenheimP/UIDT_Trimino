    data Orientation = NW | NE | SW | SE 
      deriving Show
    data Kvadrant =  I | II | III | IV 
        deriving (Show, Eq)


    -- Posmatramo trimino kao trojku (x, y, orientacija),
    -- gde je (x, y) koordinata gornjeg ćoška trimina,
    
    type Tromino = (Int, Int, Orientation)
    type Rupa = (Int, Int)

    pow2 :: Int -> Int
    pow2 n = 2 ^ n



    translate_one :: (Int,Int) -> Tromino -> Tromino
    translate_one (dx,dy) (x,y,orient) = (x + dx, y + dy, orient)

    translate :: (Int,Int) -> [Tromino] -> [Tromino]
    translate delta trominos = map (translate_one delta) trominos

    -- xflip :: Int -> [Tromino] -> [Tromino]
    -- xflip size ts =
    --     [(x, (size - 1) - y, flipO o) | (x, y, o) <- ts]
    --     where
    --         flipO NW = SW
    --         flipO SW = NW
    --         flipO NE = SE
    --         flipO SE = NE


    -- yflip :: Int -> [Tromino] -> [Tromino]
    -- yflip size ts =
    --     [((size - 1) - x, y, flipO o) | (x, y, o) <- ts]
    --     where
    --         flipO NW = NE
    --         flipO NE = NW
    --         flipO SW = SE
    --         flipO SE = SW

    base_case :: Rupa -> [Tromino]
    base_case (x, y) =
        case (x,y ) of
            (0, 0) -> [(1,1,SE)]
            (0,1) ->[(1,0,NE)]
            (1,0) ->[(0,1,SW)]
            (1,1) ->[(0,0,NW)]

    where_is_the_whole :: Int -> Rupa -> Kvadrant
    where_is_the_whole size (x, y)
        | x < half && y < half = I
        | x < half && y >= half = II
        | x >= half && y >= half = III
        | otherwise = IV
        where half = size `div` 2

    center :: Int -> Rupa -> [Tromino]
    center 2 rupa = base_case rupa
    center size rupa =
        case where_is_the_whole size rupa of
            I -> [(half, half, SE)]
            II -> [(half, half - 1, NE)]
            III -> [(half -1, half - 1, NW)]
            IV -> [(half - 1, half, SW)]
        where half = size `div` 2

    nove_rupe :: Int -> Rupa -> [Rupa]
    nove_rupe size rupa =
            case orient of
                NW -> [(x, y), (x, y + 1),rupa, (x + 1, y)]
                NE -> [ (x - 1, y),rupa, (x, y + 1),(x, y)]
                SW -> [(x, y - 1),(x, y),(x + 1, y), rupa]
                SE -> [rupa,(x - 1, y),(x, y) ,(x, y - 1)]
            where (x, y, orient) = head (center size rupa)
    
    rekurzija_rupe :: Int -> [Rupa] -> [Rupa]
    rekurzija_rupe size [(x1,y1), (x2,y2), (x3,y3), (x4,y4)] =
        [(x1,y1),(x2,y2-size `div` 2),(x3 - size `div` 2,y3 - size `div` 2),(x4 - size `div` 2,y4)]
    
    tile :: Int -> Rupa -> [Tromino]
    tile n rupa
        | n <= 0  = []
        | n == 1  = base_case rupa
        | otherwise = 
            let size = pow2 n
                center_tromino = center size rupa
                holes = nove_rupe size rupa
                rec_hole = rekurzija_rupe size holes
                prvi = tile (n - 1) (rec_hole !! 0)
                drugi = translate (0, size `div` 2) (tile (n - 1) (rec_hole !! 1))
                treci = translate (size `div` 2, size `div` 2) (tile (n - 1) (rec_hole !! 2))
                cetvrti = translate (size `div` 2, 0) (tile (n - 1) (rec_hole !! 3))
            in  center_tromino ++ prvi ++ drugi ++ treci ++ cetvrti


    -- tile :: Int -> [Tromino]
    -- tile n
    --     | n <= 0  = []
    --     | n == 1  = [(0, 0, NW)]
    --     | otherwise = 
                
    --         let m = pow2 (n - 1)
    --             base = tile (n - 1)

    --             nw = base
    --             ne = translate (m, 0) (yflip m base)
    --             sw = translate (0, m) (xflip m base)
    --             se = translate (m, m) (xflip m (yflip m base))

            
    --         in nw ++ ne ++ sw ++ se ++ center

