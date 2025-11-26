import Std.IO
import Std.Bool
import Std.Memory
import Raylib

# Tetromino shapes
# Types: 1=I, 2=O, 3=T, 4=S, 5=Z, 6=J, 7=L

def get_i_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    result: Int32 = idx if horiz else 0
    return result

def get_i_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    result: Int32 = 0 if horiz else idx
    return result

def get_o_x(idx: Int32) -> Int32:
    result: Int32 = idx % 2
    return result

def get_o_y(idx: Int32) -> Int32:
    result: Int32 = idx / 2
    return result

def get_t_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    x0: Int32 = 1 if (r == 0) else (0 if (r == 1) else (0 if (r == 2) else 1))
    x1: Int32 = 0 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 0))
    x2: Int32 = 1 if (r == 0) else (1 if (r == 1) else (2 if (r == 2) else 1))
    x3: Int32 = 2 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 2))
    result: Int32 = x0 if (idx == 0) else (x1 if (idx == 1) else (x2 if (idx == 2) else x3))
    return result

def get_t_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    y0: Int32 = 0 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 0))
    y1: Int32 = 1 if (r == 0) else (1 if (r == 1) else (0 if (r == 2) else 1))
    y2: Int32 = 1 if (r == 0) else (0 if (r == 1) else (0 if (r == 2) else 1))
    y3: Int32 = 1 if (r == 0) else (2 if (r == 1) else (0 if (r == 2) else 2))
    result: Int32 = y0 if (idx == 0) else (y1 if (idx == 1) else (y2 if (idx == 2) else y3))
    return result

def get_s_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    x0: Int32 = 1 if horiz else 0
    x1: Int32 = 2 if horiz else 0
    x2: Int32 = 0 if horiz else 1
    x3: Int32 = 1 if horiz else 1
    result: Int32 = x0 if (idx == 0) else (x1 if (idx == 1) else (x2 if (idx == 2) else x3))
    return result

def get_s_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    y0: Int32 = 0 if horiz else 0
    y1: Int32 = 0 if horiz else 1
    y2: Int32 = 1 if horiz else 1
    y3: Int32 = 1 if horiz else 2
    result: Int32 = y0 if (idx == 0) else (y1 if (idx == 1) else (y2 if (idx == 2) else y3))
    return result

def get_z_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    x0: Int32 = 0 if horiz else 1
    x1: Int32 = 1 if horiz else 0
    x2: Int32 = 1 if horiz else 1
    x3: Int32 = 2 if horiz else 0
    result: Int32 = x0 if (idx == 0) else (x1 if (idx == 1) else (x2 if (idx == 2) else x3))
    return result

def get_z_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    y0: Int32 = 0 if horiz else 0
    y1: Int32 = 0 if horiz else 1
    y2: Int32 = 1 if horiz else 1
    y3: Int32 = 1 if horiz else 2
    result: Int32 = y0 if (idx == 0) else (y1 if (idx == 1) else (y2 if (idx == 2) else y3))
    return result

def get_j_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    x0: Int32 = 0 if (r == 0) else (0 if (r == 1) else (2 if (r == 2) else 1))
    x1: Int32 = 0 if (r == 0) else (1 if (r == 1) else (0 if (r == 2) else 0))
    x2: Int32 = 1 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 1))
    x3: Int32 = 2 if (r == 0) else (0 if (r == 1) else (2 if (r == 2) else 1))
    result: Int32 = x0 if (idx == 0) else (x1 if (idx == 1) else (x2 if (idx == 2) else x3))
    return result

def get_j_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    y0: Int32 = 0 if (r == 0) else (0 if (r == 1) else (0 if (r == 2) else 0))
    y1: Int32 = 1 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 1))
    y2: Int32 = 1 if (r == 0) else (1 if (r == 1) else (1 if (r == 2) else 1))
    y3: Int32 = 1 if (r == 0) else (2 if (r == 1) else (1 if (r == 2) else 2))
    result: Int32 = y0 if (idx == 0) else (y1 if (idx == 1) else (y2 if (idx == 2) else y3))
    return result

def get_l_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    x0: Int32 = 2 if (r == 0) else (0 if (r == 1) else (0 if (r == 2) else 1))
    x1: Int32 = 0 if (r == 0) else (0 if (r == 1) else (2 if (r == 2) else 1))
    x2: Int32 = 1 if (r == 0) else (1 if (r == 1) else (2 if (r == 2) else 0))
    x3: Int32 = 2 if (r == 0) else (1 if (r == 1) else (2 if (r == 2) else 1))
    result: Int32 = x0 if (idx == 0) else (x1 if (idx == 1) else (x2 if (idx == 2) else x3))
    return result

def get_l_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    y0: Int32 = 0 if (r == 0) else (0 if (r == 1) else (1 if (r == 2) else 0))
    y1: Int32 = 1 if (r == 0) else (1 if (r == 1) else (0 if (r == 2) else 1))
    y2: Int32 = 1 if (r == 0) else (1 if (r == 1) else (0 if (r == 2) else 1))
    y3: Int32 = 1 if (r == 0) else (2 if (r == 1) else (0 if (r == 2) else 2))
    result: Int32 = y0 if (idx == 0) else (y1 if (idx == 1) else (y2 if (idx == 2) else y3))
    return result

def get_offset_x(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    result: Int32 = get_i_x(rot, idx) if (ptype == 1) else (get_o_x(idx) if (ptype == 2) else (get_t_x(rot, idx) if (ptype == 3) else (get_s_x(rot, idx) if (ptype == 4) else (get_z_x(rot, idx) if (ptype == 5) else (get_j_x(rot, idx) if (ptype == 6) else get_l_x(rot, idx))))))
    return result

def get_offset_y(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    result: Int32 = get_i_y(rot, idx) if (ptype == 1) else (get_o_y(idx) if (ptype == 2) else (get_t_y(rot, idx) if (ptype == 3) else (get_s_y(rot, idx) if (ptype == 4) else (get_z_y(rot, idx) if (ptype == 5) else (get_j_y(rot, idx) if (ptype == 6) else get_l_y(rot, idx))))))
    return result

# Collision check for a single block, returns 1 if collision, 0 if not
def check_block_bounds(grid: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32, res_ptr: VoidPtr) -> IO(Unit):
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    oob: Bool = (bx < 0) or (bx > 9) or (by > 19)
    if oob:
        store_int32(res_ptr, 1)
    else:
        if by < 0:
            store_int32(res_ptr, 0)
        else:
            val: Int32 <- load_int32(ptr_offset(grid, (bx + by * 10) * 4))
            res: Int32 = 1 if (val != 0) else 0
            store_int32(res_ptr, res)

# Check all 4 blocks for boundary collision
def check_bounds(grid: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Int32):
    res_ptr: VoidPtr <- calloc(1L, 4L)
    check_block_bounds(grid, px, py, pt, pr, 0, res_ptr)
    c0: Int32 <- load_int32(res_ptr)
    check_block_bounds(grid, px, py, pt, pr, 1, res_ptr)
    c1: Int32 <- load_int32(res_ptr)
    check_block_bounds(grid, px, py, pt, pr, 2, res_ptr)
    c2: Int32 <- load_int32(res_ptr)
    check_block_bounds(grid, px, py, pt, pr, 3, res_ptr)
    c3: Int32 <- load_int32(res_ptr)
    free(res_ptr)
    return Std.IO.return(Int32, c0 + c1 + c2 + c3)

def get_color_hex(c: Int32) -> Int32:
    result: Int32 = (0 - 16776961) if (c == 1) else (16711935 if (c == 2) else (65535 if (c == 3) else ((0 - 256) if (c == 4) else ((0 - 65281) if (c == 5) else ((0 - 5963521) if (c == 6) else (1431655935 if (c == 7) else 255))))))
    return result

def draw_block(x: Int32, y: Int32, c: Int32) -> IO(Unit):
    DrawRectangle(x * 30, y * 30, 28, 28, GetColor(get_color_hex(c)))

def draw_piece_block(px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> IO(Unit):
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    draw_block(bx, by, pt)

def draw_piece(px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Unit):
    draw_piece_block(px, py, pt, pr, 0)
    draw_piece_block(px, py, pt, pr, 1)
    draw_piece_block(px, py, pt, pr, 2)
    draw_piece_block(px, py, pt, pr, 3)
    return Std.IO.return(Unit, tt)

def lock_block(grid: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> IO(Unit):
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    valid: Bool = (bx >= 0) and (bx < 10) and (by >= 0) and (by < 20)
    if valid:
        store_int32(ptr_offset(grid, (bx + by * 10) * 4), pt)
    else:
        return Std.IO.return(Unit, tt)

def lock_piece(grid: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Unit):
    lock_block(grid, px, py, pt, pr, 0)
    lock_block(grid, px, py, pt, pr, 1)
    lock_block(grid, px, py, pt, pr, 2)
    lock_block(grid, px, py, pt, pr, 3)
    return Std.IO.return(Unit, tt)

def draw_cell(grid: VoidPtr, i: Int32) -> IO(Unit):
    cell: Int32 <- load_int32(ptr_offset(grid, i * 4))
    if cell != 0:
        x: Int32 = i % 10
        y: Int32 = i / 10
        draw_block(x, y, cell)
    else:
        return Std.IO.return(Unit, tt)

def draw_grid_rec(grid: VoidPtr, i: Int32) -> IO(Unit):
    if i >= 200:
        return Std.IO.return(Unit, tt)
    else:
        draw_cell(grid, i)
        draw_grid_rec(grid, i + 1)

def draw_grid(grid: VoidPtr) -> IO(Unit):
    draw_grid_rec(grid, 0)

def random_piece(seed: Int32) -> Int32:
    result: Int32 = (seed % 7) + 1
    return result

# Read grid cell - returns 0 if empty or out of bounds above
def read_cell(grid: VoidPtr, x: Int32, y: Int32) -> IO(Unit):
    if y < 0:
        return Std.IO.return(Unit, tt)
    else:
        if (x < 0) or (x > 9) or (y > 19):
            return Std.IO.return(Unit, tt)
        else:
            return Std.IO.return(Unit, tt)

def loop(grid: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32, timer: Int32, seed: Int32) -> IO(Unit):
    should_close: Bool <- WindowShouldClose(tt)
    if should_close:
        return Std.IO.return(Unit, tt)
    else:
        key_left: Bool <- IsKeyPressed(263)
        key_right: Bool <- IsKeyPressed(262)
        key_down: Bool <- IsKeyDown(264)
        key_up: Bool <- IsKeyPressed(265)
        
        # Calculate movement
        dx: Int32 = (0 - 1) if key_left else (1 if key_right else 0)
        new_px: Int32 = px + dx
        new_pr: Int32 = ((pr + 1) % 4) if key_up else pr
        
        # Check horizontal collision (bounds only for simplicity)
        h_coll: Int32 <- check_bounds(grid, new_px, py, pt, pr)
        final_px: Int32 = px if (h_coll > 0) else new_px
        
        # Check rotation collision
        r_coll: Int32 <- check_bounds(grid, px, py, pt, new_pr)
        final_pr: Int32 = pr if (r_coll > 0) else new_pr
        
        # Calculate drop
        drop_rate: Int32 = 5 if key_down else 30
        should_drop: Bool = (timer % drop_rate) == 0
        new_py: Int32 = (py + 1) if should_drop else py
        
        # Check vertical collision
        v_coll: Int32 <- check_bounds(grid, final_px, new_py, pt, final_pr)
        need_lock: Bool = (v_coll > 0) and should_drop
        
        if need_lock:
            lock_piece(grid, final_px, py, pt, final_pr)
            new_seed: Int32 = seed * 1103515245 + 12345
            new_type: Int32 = random_piece(new_seed)
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            draw_grid(grid)
            draw_piece(4, 0, new_type, 0)
            EndDrawing(tt)
            loop(grid, 4, 0, new_type, 0, 0, new_seed)
        else:
            final_py: Int32 = py if (v_coll > 0) else new_py
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            draw_grid(grid)
            draw_piece(final_px, final_py, pt, final_pr)
            EndDrawing(tt)
            loop(grid, final_px, final_py, pt, final_pr, timer + 1, seed)

def main() -> IO(Unit):
    InitWindow(300, 600, "CertiJSON Tetris")
    SetTargetFPS(60)
    grid: VoidPtr <- calloc(200L, 4L)
    start_type: Int32 = random_piece(42)
    loop(grid, 4, 0, start_type, 0, 0, 42)
    free(grid)
    CloseWindow(tt)
