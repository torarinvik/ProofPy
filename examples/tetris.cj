import Std.IO
import Std.Bool
import Std.Memory
import Std.Int
import Raylib

# =============================================================================
# REFINEMENT TYPES FOR GAME SAFETY
# =============================================================================
# These types ensure compile-time bounds checking, preventing:
# - Out-of-bounds array access
# - Invalid piece/rotation indices
# - Buffer overflows

# Grid dimensions (constants)
def GRID_WIDTH() -> Int32:
    10

def GRID_HEIGHT() -> Int32:
    20

def GRID_SIZE() -> Int32:
    200

# Refinement Types for bounded values
# A GridX is an integer in [0, 10)
def GridX() -> Type:
    {x: Int32 | x >= 0 and x < 10}

# A GridY is an integer in [0, 20)
def GridY() -> Type:
    {y: Int32 | y >= 0 and y < 20}

# A GridIndex is a valid index into the 200-cell grid
def GridIndex() -> Type:
    {i: Int32 | i >= 0 and i < 200}

# PieceType: valid tetromino types (1-7)
def PieceType() -> Type:
    {p: Int32 | p >= 1 and p <= 7}

# Rotation: 0-3 representing 0°, 90°, 180°, 270°
def Rotation() -> Type:
    {r: Int32 | r >= 0 and r < 4}

# BlockIndex: 0-3 for the 4 blocks in a piece
def BlockIndex() -> Type:
    {i: Int32 | i >= 0 and i < 4}

# ColorCode: valid color values (0-7)
def ColorCode() -> Type:
    {c: Int32 | c >= 0 and c <= 7}

# =============================================================================
# HELPER FUNCTIONS WITH BOUNDS PROOFS
# =============================================================================

# Safe grid index calculation with bounds checking
# Converts (x, y) coordinates to a linear grid index
# Precondition: 0 <= x < 10, 0 <= y < 20
# Postcondition: 0 <= result < 200
def grid_index(x: Int32, y: Int32) -> Int32:
    return x + y * 10

# Validate if a coordinate is within grid bounds
def in_bounds(x: Int32, y: Int32) -> Bool:
    return (x >= 0) and (x < 10) and (y >= 0) and (y < 20)

# Safe rotation normalization (always returns 0-3)
def normalize_rotation(r: Int32) -> Rotation:
    raw : Int32 = r % 4
    if raw < 0:
        return raw + 4
    else:
        return raw

# Safe piece type validation
def valid_piece_type(p: Int32) -> Bool:
    return (p >= 1) and (p <= 7)

# =============================================================================
# SAFE MEMORY ACCESS PRIMITIVES
# =============================================================================
# These wrappers ensure all grid accesses are bounds-checked

# Read a cell from the grid with bounds checking
# Returns 0 (empty) for out-of-bounds coordinates
def safe_grid_read(view: VoidPtr, x: Int32, y: Int32) -> Int32:
    if in_bounds(x, y):
        idx : Int64 = Std.Memory.int32_to_int64(grid_index(x, y))
        offset : Int64 = Std.Int.mul64(idx, 4L)
        ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
        Std.Memory.unsafe_load_int32(ptr)
    else:
        0

# Write a cell to the grid with bounds checking
# No-op for out-of-bounds coordinates
def safe_grid_write(view: VoidPtr, x: Int32, y: Int32, val: Int32) -> Unit:
    if in_bounds(x, y):
        idx : Int64 = Std.Memory.int32_to_int64(grid_index(x, y))
        offset : Int64 = Std.Int.mul64(idx, 4L)
        ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
        _ : Int32 = Std.Memory.unsafe_store_int32(ptr, val)

# =============================================================================
# TETROMINO SHAPE DEFINITIONS
# =============================================================================
# Types: 1=I, 2=O, 3=T, 4=S, 5=Z, 6=J, 7=L
# Each piece consists of 4 blocks with relative offsets

def get_i_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            1 if horiz else 0
        case 2:
            2 if horiz else 0
        case 3:
            3 if horiz else 0

def get_i_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            0 if horiz else 2
        case 3:
            0 if horiz else 3

def get_o_x(idx: Int32) -> Int32:
    match idx:
        case 0:
            0
        case 1:
            1
        case 2:
            0
        case 3:
            1

def get_o_y(idx: Int32) -> Int32:
    match idx:
        case 0:
            0
        case 1:
            0
        case 2:
            1
        case 3:
            1

def get_t_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    1
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    1
                case 1:
                    1
                case 2:
                    1
                case 3:
                    0
        case 2:
            match idx:
                case 0:
                    1
                case 1:
                    2
                case 2:
                    1
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1

def get_t_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    1
        case 2:
            match idx:
                case 0:
                    1
                case 1:
                    0
                case 2:
                    0
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    1

def get_s_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            1 if horiz else 0
        case 1:
            2 if horiz else 0
        case 2:
            0 if horiz else 1
        case 3:
            1 if horiz else 1

def get_s_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            1 if horiz else 1
        case 3:
            1 if horiz else 2

def get_z_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 1
        case 1:
            1 if horiz else 1
        case 2:
            1 if horiz else 0
        case 3:
            2 if horiz else 0

def get_z_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            1 if horiz else 1
        case 3:
            1 if horiz else 2

def get_j_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    0
                case 3:
                    0
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2
        case 3:
            match idx:
                case 0:
                    1
                case 1:
                    1
                case 2:
                    1
                case 3:
                    0

def get_j_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2

def get_l_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    2
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1

def get_l_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2

def get_offset_x(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    match ptype:
        case 1:
            get_i_x(rot, idx)
        case 2:
            get_o_x(idx)
        case 3:
            get_t_x(rot, idx)
        case 4:
            get_s_x(rot, idx)
        case 5:
            get_z_x(rot, idx)
        case 6:
            get_j_x(rot, idx)
        case 7:
            get_l_x(rot, idx)
        case _:
            0

def get_offset_y(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    match ptype:
        case 1:
            get_i_y(rot, idx)
        case 2:
            get_o_y(idx)
        case 3:
            get_t_y(rot, idx)
        case 4:
            get_s_y(rot, idx)
        case 5:
            get_z_y(rot, idx)
        case 6:
            get_j_y(rot, idx)
        case 7:
            get_l_y(rot, idx)
        case _:
            0

# =============================================================================
# COLLISION DETECTION (Using Safe Memory Access)
# =============================================================================

def check_block_bounds(view: VoidPtr, px: GridX, py: Int32, pt: PieceType, pr: Rotation, idx: BlockIndex) -> Int32:
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    
    # Wall collision check
    if (bx < 0) or (bx >= 10) or (by >= 20):
        1
    else:
        # Above top of screen is valid (for spawning)
        if by < 0:
            0
        else:
            # Check grid cell occupation using safe accessor
            cell : Int32 = safe_grid_read(view, bx, by)
            if cell != 0:
                1
            else:
                0

# Logical predicate: a block is "standing" on something solid (bottom or occupied cell below)
def is_block_supported(view: VoidPtr, bx: Int32, by: Int32) -> Bool:
    # Below bottom of screen is not allowed
    if by < 0:
        False
    else:
        if by == 19:
            True
        else:
            # Safe read; for by in [0,18], by+1 is still in [0,19]
            below : Int32 = safe_grid_read(view, bx, by + 1)
            return below != 0

# Proof-style helper: when a piece can no longer move down, at least one block is supported
def assert_landing_reason(grid: Int64, px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32, found: Bool) -> Bool:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    if idx >= 4:
        # Postcondition: some block is supported
        found
    else:
        bx : Int32 = px + get_offset_x(pt, pr, idx)
        by : Int32 = py + get_offset_y(pt, pr, idx)
        this_supported : Bool = is_block_supported(view, bx, by)
        assert_landing_reason(grid, px, py, pt, pr, idx + 1, found or this_supported)

# Proof check: verify landing reason and fail visibly if invalid
def check_landing_proof(grid: Int64, landing_ok: Bool) -> Unit:
    if landing_ok:
        tt
    else:
        view_fail : VoidPtr = Std.Memory.int64_to_ptr(grid)
        safe_grid_write(view_fail, 0, 0, 0 - 3)

# Check all 4 blocks of a piece for collision
# Returns: 0 if all positions valid, >0 if any collision
def check_bounds(grid: Int64, px: GridX, py: Int32, pt: PieceType, pr: Rotation) -> Int32:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    c0 : Int32 = check_block_bounds(view, px, py, pt, pr, 0)
    c1 : Int32 = check_block_bounds(view, px, py, pt, pr, 1)
    c2 : Int32 = check_block_bounds(view, px, py, pt, pr, 2)
    c3 : Int32 = check_block_bounds(view, px, py, pt, pr, 3)
    return c0 + c1 + c2 + c3

# =============================================================================
# COLOR SYSTEM (Type-Safe Color Mapping)
# =============================================================================

def get_color_hex(c: Int32) -> Int32:
    match c:
        case 1:
            0 - 16776961
        case 2:
            16711935
        case 3:
            65535
        case 4:
            0 - 256
        case 5:
            0 - 65281
        case 6:
            0 - 5963521
        case 7:
            1431655935
        case _:
            255

# =============================================================================
# RENDERING (Type-Safe Drawing Functions)
# =============================================================================

def draw_block(x: Int32, y: Int32, c: Int32) -> IO(Unit):
    DrawRectangle(x * 30, y * 30, 28, 28, GetColor(get_color_hex(c)))

def draw_piece_block(px: GridX, py: Int32, pt: PieceType, pr: Rotation, idx: BlockIndex) -> IO(Unit):
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    draw_block(bx, by, pt)

def draw_piece(px: GridX, py: Int32, pt: PieceType, pr: Rotation) -> IO(Unit):
    draw_piece_block(px, py, pt, pr, 0)
    draw_piece_block(px, py, pt, pr, 1)
    draw_piece_block(px, py, pt, pr, 2)
    draw_piece_block(px, py, pt, pr, 3)
    return Std.IO.return(Unit, tt)

# =============================================================================
# PIECE LOCKING (Using Safe Memory Access)
# =============================================================================

# Lock a single block of a piece into the grid
# Uses safe_grid_write for bounds-checked memory access
def lock_block(view: VoidPtr, px: GridX, py: Int32, pt: PieceType, pr: Rotation, idx: BlockIndex) -> Unit:
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    # safe_grid_write handles bounds checking internally
    _ : Unit = safe_grid_write(view, bx, by, pt)

# Proof-style block checker: after locking, the block must be on-grid and equal to pt
def assert_block_locked(view: VoidPtr, px: GridX, py: Int32, pt: PieceType, pr: Rotation, idx: BlockIndex) -> Unit:
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)

    # Invariant: all locked blocks are inside the visible grid
    inb : Bool = in_bounds(bx, by)
    if inb:
        cell : Int32 = safe_grid_read(view, bx, by)
        correct : Bool = (cell == pt)
        if correct:
            tt
        else:
            _ : Unit = safe_grid_write(view, 0, 0, 0 - 2)
    else:
        # Force a detectable failure by writing an impossible value
        _ : Unit = safe_grid_write(view, 0, 0, 0 - 1)

# Proof-style piece checker: all four blocks are properly locked
def assert_piece_locked_on_grid(grid: Int64, px: GridX, py: Int32, pt: PieceType, pr: Rotation) -> Unit:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    _ : Unit = assert_block_locked(view, px, py, pt, pr, 0)
    _ : Unit = assert_block_locked(view, px, py, pt, pr, 1)
    _ : Unit = assert_block_locked(view, px, py, pt, pr, 2)
    _ : Unit = assert_block_locked(view, px, py, pt, pr, 3)

# =============================================================================
# LINE CLEARING (Using Safe Memory Access + Recursion)
# =============================================================================
# These functions are implemented recursively instead of with while loops
# for better reasoning about termination and correctness

# Check if a row is completely filled (recursive over columns)
# Precondition: y is a valid row index (0 <= y < 20)
def check_row_full(view: VoidPtr, y: Int32, x: Int32) -> Bool:
    if x >= 10:
        True
    else:
        cell : Int32 = safe_grid_read(view, x, y)
        if cell == 0:
            False
        else:
            check_row_full(view, y, x + 1)

# Shift a row down by one (copy from y-1 to y)
# Precondition: y > 0 (not shifting into row above screen)
def shift_row_down(view: VoidPtr, y: Int32, x: Int32) -> Unit:
    if x < 10:
        val : Int32 = safe_grid_read(view, x, y - 1)
        _ : Unit = safe_grid_write(view, x, y, val)
        shift_row_down(view, y, x + 1)

# Clear the top row (set all cells to 0)
def clear_top_row(view: VoidPtr, x: Int32) -> Unit:
    if x < 10:
        _ : Unit = safe_grid_write(view, x, 0, 0)
        clear_top_row(view, x + 1)

# Shift all rows above y down by one, then clear top
def shift_rows(view: VoidPtr, y: Int32) -> Unit:
    if y > 0:
        _ : Unit = shift_row_down(view, y, 0)
        shift_rows(view, y - 1)
    else:
        _ : Unit = clear_top_row(view, 0)

# Check all rows for full lines and clear them (recursive)
# Invariant: y decreases each iteration until y < 0 (termination guaranteed)
def check_lines_rec(view: VoidPtr, y: Int32) -> Unit:
    if y >= 0:
        if check_row_full(view, y, 0):
            _ : Unit = shift_rows(view, y)
            check_lines_rec(view, y)
        else:
            check_lines_rec(view, y - 1)

# Lock entire piece into grid and check for completed lines
def lock_piece(grid: Int64, px: GridX, py: Int32, pt: PieceType, pr: Rotation) -> Unit:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    _ : Unit = lock_block(view, px, py, pt, pr, 0)
    _ : Unit = lock_block(view, px, py, pt, pr, 1)
    _ : Unit = lock_block(view, px, py, pt, pr, 2)
    _ : Unit = lock_block(view, px, py, pt, pr, 3)
    
    _ : Unit = check_lines_rec(view, 19)
    # Postcondition proof: the locked piece obeys the grid invariant
    _ : Unit = assert_piece_locked_on_grid(grid, px, py, pt, pr)

# =============================================================================
# GRID RENDERING (Recursive with Bounds)
# =============================================================================

# Draw a single cell if non-empty
def draw_cell(view: VoidPtr, i: Int32) -> IO(Unit):
    # Safe to compute x,y since we control the iteration bounds
    x : Int32 = i % 10
    y : Int32 = i / 10
    cell : Int32 = safe_grid_read(view, x, y)
    if cell != 0:
        draw_block(x, y, cell)
    else:
        Std.IO.return(Unit, tt)

def draw_grid_rec(view: VoidPtr, i: Int32) -> IO(Unit):
    if i < 200:
        draw_cell(view, i)
        draw_grid_rec(view, i + 1)
    else:
        Std.IO.return(Unit, tt)

def draw_grid(grid: Int64) -> IO(Unit):
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    draw_grid_rec(view, 0)

# =============================================================================
# RANDOM NUMBER GENERATOR (Deterministic LCG)
# =============================================================================
# Linear Congruential Generator for piece selection
# Postcondition: 1 <= result <= 7 (valid piece type)
def random_piece(seed: Int32) -> PieceType:
    s : Int32 = seed % 7
    pos_s : Int32 = s if (s >= 0) else (0 - s)
    return pos_s + 1

# =============================================================================
# GAME LOOP (Main Game Logic with Type Safety)
# =============================================================================
# All state is passed explicitly (no mutation)
# Recursively processes frames until window closes
#
# Invariants maintained:
# - pt is always a valid piece type (1-7)
# - pr is always a valid rotation (0-3)
# - Grid accesses are bounds-checked via safe_grid_read/write

def game_loop(grid: Int64, px: GridX, py: Int32, pt: PieceType, pr: Rotation, timer: Int32, seed: Int32, game_over: Bool) -> IO(Unit):
    should_close : Bool <- WindowShouldClose(tt)
    if should_close:
        Std.IO.return(Unit, tt)
    else:
        if game_over:
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            draw_grid(grid)
            DrawText("GAME OVER", 50, 250, 40, GetColor(0 - 16776961))
            EndDrawing(tt)
            game_loop(grid, px, py, pt, pr, timer, seed, game_over)
        else:
            # Input handling
            key_left : Bool <- IsKeyPressed(263)
            key_right : Bool <- IsKeyPressed(262)
            key_down : Bool <- IsKeyDown(264)
            key_up : Bool <- IsKeyPressed(265)
            
            # Horizontal movement with collision check
            dx : Int32 = (0 - 1) if key_left else (1 if key_right else 0)
    
            new_px : GridX = px + dx
            final_px : GridX = new_px if (check_bounds(grid, new_px, py, pt, pr) == 0) else px
            
            # Rotation with collision check
            # normalize_rotation ensures result is in [0,4)
            new_pr : Rotation = normalize_rotation(pr + 1)
            final_pr : Rotation = new_pr if (key_up and (check_bounds(grid, final_px, py, pt, new_pr) == 0)) else pr
            
            # Vertical movement (Gravity)
            drop_rate : Int32 = 5 if key_down else 30
            
            should_drop : Bool = (timer % drop_rate) == 0
            
            if should_drop:
                new_py : Int32 = py + 1
                
                # DEBUG: Print drop attempt info
                Std.IO.print_line("=== DROP ATTEMPT ===")
                
                # Check if we can move down
                collision : Int32 = check_bounds(grid, final_px, new_py, pt, final_pr)
                
                if collision == 0:
                    Std.IO.print_line("-> Moving down (no collision)")
                    # Drawing
                    BeginDrawing(tt)
                    ClearBackground(GetColor(255))
                    draw_grid(grid)
                    draw_piece(final_px, new_py, pt, final_pr)
                    EndDrawing(tt)
                    game_loop(grid, final_px, new_py, pt, final_pr, timer + 1, seed, game_over)
                else:
                    Std.IO.print_line("-> COLLISION DETECTED - LOCKING PIECE")
                    
                    # Proof obligation: we can no longer move down, so some block must be supported
                    landing_ok : Bool = assert_landing_reason(grid, final_px, py, pt, final_pr, 0, False)
                    # Print landing_ok as 0/1 (no inline if expressions)
                    if landing_ok:
                        Std.IO.print_line("landing_ok = True")
                    else:
                        Std.IO.print_line("landing_ok = False")
                    
                    # If landing_ok is False, a logic error occurred; trigger a visible failure
                    check_result : Unit = check_landing_proof(grid, landing_ok)

                    # Lock piece
                    Std.IO.print_line("Calling lock_piece...")
                    _ : Unit = lock_piece(grid, final_px, py, pt, final_pr)
                    
                    # Spawn new piece (random_piece guarantees 1 <= result <= 7)
                    new_seed : Int32 = (seed * 1103515245) + 12345
                    new_pt : Int32 = random_piece(new_seed)
                    new_px_spawn : Int32 = 4
                    new_py_spawn : Int32 = 0
                    new_pr_spawn : Int32 = 0
                    
                    # Check Game Over
                    new_game_over : Bool = check_bounds(grid, new_px_spawn, new_py_spawn, new_pt, new_pr_spawn) > 0
                    
                    # Drawing
                    BeginDrawing(tt)
                    ClearBackground(GetColor(255))
                    draw_grid(grid)
                    draw_piece(final_px, py, pt, final_pr)
                    EndDrawing(tt)
                    
                    game_loop(grid, new_px_spawn, new_py_spawn, new_pt, new_pr_spawn, timer + 1, new_seed, new_game_over)
            else:
                # Drawing
                BeginDrawing(tt)
                ClearBackground(GetColor(255))
                draw_grid(grid)
                draw_piece(final_px, py, pt, final_pr)
                EndDrawing(tt)
                game_loop(grid, final_px, py, pt, final_pr, timer + 1, seed, game_over)

# =============================================================================
# MAIN ENTRY POINT
# =============================================================================
# Initializes game state with verified initial conditions:
# - Grid allocated with GRID_SIZE (200) cells
# - Initial piece type from random_piece (guaranteed 1-7)
# - Initial rotation 0 (valid rotation)
# - Initial position (4, 0) for centered spawn

def main() -> IO(Unit):
    InitWindow(300, 600, "ProofPy Tetris")
    SetTargetFPS(60)
    
    # Allocate grid: 200 cells * 4 bytes per Int32 = 800 bytes
    # calloc zeros memory, so all cells start empty (0)
    grid_ptr : VoidPtr <- Std.Memory.calloc(200L, 4L)
    grid : Int64 = Std.Memory.ptr_to_int64(grid_ptr)
    
    # Initial game state
    # px: piece x position (center of grid)
    # py: piece y position (top of grid)  
    # pt: piece type (1-7, from random_piece)
    # pr: piece rotation (0-3)
    px : GridX = 4
    py : Int32 = 0
    pt : PieceType = random_piece(42)  # Guaranteed: 1 <= pt <= 7
    pr : Rotation = 0                  # Guaranteed: 0 <= pr < 4
    timer : Int32 = 0
    seed : Int32 = 42
    game_over : Bool = False
    
    game_loop(grid, px, py, pt, pr, timer, seed, game_over)

    # Cleanup
    grid_ptr_free : VoidPtr = Std.Memory.int64_to_ptr(grid)
    Std.Memory.free(grid_ptr_free)
    CloseWindow(tt)
    return Std.IO.return(Unit, tt)
