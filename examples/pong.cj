import Std.IO
import Std.Bool
import Raylib

def loop(ball_x: Int32, ball_y: Int32, ball_dx: Int32, ball_dy: Int32, p1_y: Int32, p2_y: Int32, s1: Int32, s2: Int32) -> IO(Unit):
    should_close: Bool <- WindowShouldClose(tt)
    if should_close:
        return Std.IO.return(Unit, tt)
    else:
        key_w: Bool <- IsKeyDown(87)
        key_s: Bool <- IsKeyDown(83)
        key_up: Bool <- IsKeyDown(265)
        key_down: Bool <- IsKeyDown(264)
        
        BeginDrawing(tt)
        ClearBackground(GetColor(255))
        
        # Draw Player 1
        p1_y_next: Int32 = (p1_y - 5) if key_w else ((p1_y + 5) if key_s else p1_y)
        DrawRectangle(10, p1_y_next, 20, 100, GetColor(-1))
        
        # Draw Player 2
        p2_y_next: Int32 = (p2_y - 5) if key_up else ((p2_y + 5) if key_down else p2_y)
        DrawRectangle(770, p2_y_next, 20, 100, GetColor(-1))
        
        # Calculate next ball position
        ball_x_next_temp: Int32 = ball_x + ball_dx
        ball_y_next_temp: Int32 = ball_y + ball_dy
        
        # Collision logic
        s2_next: Int32 = (s2 + 1) if (ball_x_next_temp < 0) else s2
        s1_next: Int32 = (s1 + 1) if (ball_x_next_temp > 800) else s1
        
        reset: Bool = (ball_x_next_temp < 0) or (ball_x_next_temp > 800)
        ball_x_next: Int32 = 400 if reset else ball_x_next_temp
        ball_y_next: Int32 = 225 if reset else ball_y_next_temp
        
        hit_p1: Bool = (ball_x_next_temp < 20) and (ball_y_next_temp > p1_y) and (ball_y_next_temp < (p1_y + 100))
        hit_p2: Bool = (ball_x_next_temp > 760) and (ball_y_next_temp > p2_y) and (ball_y_next_temp < (p2_y + 100))
        
        ball_dx_next: Int32 = (0 - ball_dx) if (hit_p1 or hit_p2) else ball_dx
        
        hit_wall_y: Bool = (ball_y_next_temp < 0) or (ball_y_next_temp > 430)
        ball_dy_next: Int32 = (0 - ball_dy) if hit_wall_y else ball_dy
        
        DrawRectangle(ball_x_next, ball_y_next, 20, 20, GetColor(-1))
        
        DrawText(TextFormat_Int("%d", s1_next), 200, 20, 40, GetColor(-1))
        DrawText(TextFormat_Int("%d", s2_next), 600, 20, 40, GetColor(-1))
        
        EndDrawing(tt)
        
        return loop(ball_x_next, ball_y_next, ball_dx_next, ball_dy_next, p1_y_next, p2_y_next, s1_next, s2_next)

def main() -> IO(Unit):
    InitWindow(800, 450, "CertiJSON Pong")
    SetTargetFPS(60)
    loop(400, 225, 5, 5, 175, 175, 0, 0)
    CloseWindow(tt)
