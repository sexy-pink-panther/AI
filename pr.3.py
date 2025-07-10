import copy

class FutoshikiCSP:
    def __init__(self, size, grid, inequalities):
        self.size = size  # اندازه جدول (n x n)
        self.grid = grid  # جدول اولیه شامل اعداد و صفر برای خانه‌های خالی
        self.ineq = inequalities  # لیست قیود نابرابری (x1, y1, x2, y2, op)
        self.domains = {}  # دامنه ممکن برای هر خانه خالی
        self.backtracks = 0  # شمارنده تعداد بازگشت‌ها
        self.init_domains()  # مقداردهی اولیه دامنه‌ها

    def init_domains(self):
        # مقداردهی دامنه برای هر خانه: اعداد 1 تا n اگر خانه خالی باشد
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j] == 0:
                    self.domains[(i, j)] = list(range(1, self.size + 1))
                else:
                    self.domains[(i, j)] = [self.grid[i][j]]

    def is_complete(self):
        # بررسی کامل بودن جدول (بدون صفر)
        for row in self.grid:
            if 0 in row:
                return False
        return True

    def is_consistent(self, var, value):
        row, col = var
        # بررسی عدم تکرار مقدار در سطر و ستون
        for j in range(self.size):
            if j != col and self.grid[row][j] == value:
                return False
        for i in range(self.size):
            if i != row and self.grid[i][col] == value:
                return False
        # بررسی رعایت قیود نابرابری با خانه‌های دیگر
        for (x1, y1, x2, y2, op) in self.ineq:
            if (x1, y1) == var and self.grid[x2][y2] != 0:
                if op == '<' and value > self.grid[x2][y2]:
                    return False
                if op == '>' and value < self.grid[x2][y2]:
                    return False
            elif (x2, y2) == var and self.grid[x1][y1] != 0:
                if op == '<' and self.grid[x1][y1] > value:
                    return False
                if op == '>' and self.grid[x1][y1] < value:
                    return False
        return True

    def simple_backtrack(self):
        # الگوریتم بازگشت ساده (backtracking)
        if self.is_complete():
            return True
        var = self.select_next_variable()
        for value in self.domains[var]:
            if self.is_consistent(var, value):
                self.grid[var[0]][var[1]] = value
                if self.simple_backtrack():
                    return True
                self.grid[var[0]][var[1]] = 0
        self.backtracks += 1
        return False

    def select_next_variable(self):
        # انتخاب اولین متغیر خالی (استراتژی ساده)
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j] == 0:
                    return (i, j)
        return None

    def optimized_backtrack(self, use_fc=True, use_ac=True):
        # الگوریتم بهینه با MRV، LCV، FC و AC-2
        if self.is_complete():
            return True
        var = self.select_mrv_variable()
        for value in self.order_lcv_values(var):
            if self.is_consistent(var, value):
                old_grid = [row[:] for row in self.grid]
                old_domains = {k: v[:] for k, v in self.domains.items()}
                self.grid[var[0]][var[1]] = value
                self.domains[var] = [value]
                if use_fc and not self.forward_checking(var):
                    self.restore_state(old_grid, old_domains)
                    continue
                if use_ac and not self.ac2():
                    self.restore_state(old_grid, old_domains)
                    continue
                if self.optimized_backtrack(use_fc, use_ac):
                    return True
                self.restore_state(old_grid, old_domains)
        self.backtracks += 1
        return False

    def forward_checking(self, var):
        # حذف مقادیر ناسازگار از دامنه خانه‌های مرتبط
        row, col = var
        value = self.grid[row][col]
        for j in range(self.size):
            if j != col and value in self.domains[(row, j)]:
                self.domains[(row, j)].remove(value)
                if not self.domains[(row, j)]:
                    return False
        for i in range(self.size):
            if i != row and value in self.domains[(i, col)]:
                self.domains[(i, col)].remove(value)
                if not self.domains[(i, col)]:
                    return False
        for (x1, y1, x2, y2, op) in self.ineq:
            if (x1, y1) == var and self.grid[x2][y2] == 0:
                for val in self.domains[(x2, y2)][:]:
                    if not self.check_inequality(value, val, op):
                        self.domains[(x2, y2)].remove(val)
                        if not self.domains[(x2, y2)]:
                            return False
            if (x2, y2) == var and self.grid[x1][y1] == 0:
                for val in self.domains[(x1, y1)][:]:
                    if not self.check_inequality(val, value, op):
                        self.domains[(x1, y1)].remove(val)
                        if not self.domains[(x1, y1)]:
                            return False
        return True

    def ac2(self):
        # پیاده‌سازی الگوریتم AC-2 برای حفظ همخوانی مقادیر
        queue = self.build_arc_queue()
        while queue:
            (xi, xj) = queue.pop(0)
            if self.revise(xi, xj):
                if not self.domains[xi]:
                    return False
                for xk in self.get_neighbors(xi):
                    if xk != xj:
                        queue.append((xk, xi))
        return True

    def select_mrv_variable(self):
        # انتخاب متغیر با کمترین دامنه (MRV)
        unassigned = [v for v in self.domains if self.grid[v[0]][v[1]] == 0]
        return min(unassigned, key=lambda v: len(self.domains[v])) if unassigned else None

    def order_lcv_values(self, var):
        # مرتب‌سازی مقادیر دامنه بر اساس کمترین محدودیت (LCV)
        def count_constraints(val):
            constraints = 0
            row, col = var
            for i in range(self.size):
                if (row, i) in self.domains and i != col and val in self.domains[(row, i)]:
                    constraints += 1
                if (i, col) in self.domains and i != row and val in self.domains[(i, col)]:
                    constraints += 1
            for (x1, y1, x2, y2, op) in self.ineq:
                if (x1, y1) == var and (x2, y2) in self.domains:
                    for other_val in self.domains[(x2, y2)]:
                        if not self.check_inequality(val, other_val, op):
                            constraints += 1
                elif (x2, y2) == var and (x1, y1) in self.domains:
                    for other_val in self.domains[(x1, y1)]:
                        if not self.check_inequality(other_val, val, op):
                            constraints += 1
            return constraints
        return sorted(self.domains[var], key=count_constraints)

    def restore_state(self, old_grid, old_domains):
        # بازگرداندن وضعیت قبلی جدول و دامنه‌ها
        self.grid = [row[:] for row in old_grid]
        self.domains = {k: v[:] for k, v in old_domains.items()}

    def check_inequality(self, a, b, op):
        # بررسی برقراری قید نابرابری
        return a < b if op == '<' else a > b

    def build_arc_queue(self):
        # ساخت صف از یال‌های محدودیت بین خانه‌ها برای AC-2
        queue = []
        for (x1, y1) in self.domains:
            for j in range(self.size):
                if j != y1 and (x1, j) in self.domains:
                    queue.append(((x1, y1), (x1, j)))
            for i in range(self.size):
                if i != x1 and (i, y1) in self.domains:
                    queue.append(((x1, y1), (i, y1)))
            for (a1, b1, a2, b2, op) in self.ineq:
                if (a1, b1) == (x1, y1) and (a2, b2) in self.domains:
                    queue.append(((x1, y1), (a2, b2)))
                elif (a2, b2) == (x1, y1) and (a1, b1) in self.domains:
                    queue.append(((x1, y1), (a1, b1)))
        return queue

    def revise(self, xi, xj):
        # حذف مقادیر ناسازگار از دامنه xi در برابر xj
        revised = False
        for val in self.domains[xi][:]:
            if not any(self.is_arc_consistent(val, other_val, xi, xj) for other_val in self.domains[xj]):
                self.domains[xi].remove(val)
                revised = True
        return revised

    def is_arc_consistent(self, val_i, val_j, xi, xj):
        # بررسی سازگاری مقادیر برای یال xi -> xj
        if xi[0] == xj[0] or xi[1] == xj[1]:
            if val_i == val_j:
                return False
        for (a1, b1, a2, b2, op) in self.ineq:
            if (a1, b1) == xi and (a2, b2) == xj:
                return self.check_inequality(val_i, val_j, op)
            elif (a1, b1) == xj and (a2, b2) == xi:
                return self.check_inequality(val_j, val_i, op)
        return True

    def get_neighbors(self, var):
        # یافتن همسایه‌های یک متغیر برای AC-2
        neighbors = set()
        row, col = var
        for i in range(self.size):
            if i != row and (i, col) in self.domains:
                neighbors.add((i, col))
            if i != col and (row, i) in self.domains:
                neighbors.add((row, i))
        for (x1, y1, x2, y2, _) in self.ineq:
            if (x1, y1) == var and (x2, y2) in self.domains:
                neighbors.add((x2, y2))
            elif (x2, y2) == var and (x1, y1) in self.domains:
                neighbors.add((x1, y1))
        return neighbors

import copy

def main():
    # تعیین اندازه جدول (جدول 5 در 5)
    size = 7

    # تعریف جدول اولیه پازل Futoshiki.
    # صفرها نشان‌دهنده سلول‌هایی هستند که باید مقداردهی شوند.
    # اعداد غیر صفر (مثلاً 3 و 5 در سطر سوم، و 2 در سطر چهارم) خانه‌های از پیش مقداردهی‌شده هستند (constraint اولیه).
    grid = [
        [0, 0, 0, 0, 4, 0, 0],
        [0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0],
        [0, 6, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 5],
        [0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 3, 0, 0, 0],
    ]

    # تعریف قیود نابرابری بین سلول‌ها.
    # هر نابرابری به صورت یک 5‌تایی مشخص می‌شود: (سطر1، ستون1، سطر2، ستون2، علامت)
    # به عنوان مثال: (0,0,0,1,'>') یعنی خانه [0][0] > خانه [0][1]
    inequalities = [
        # ردیف اول: خانه اول باید بزرگ‌تر از خانه دوم باشد
        (0, 0, 0, 1, '>'),

        # ردیف دوم: خانه وسط بزرگ‌تر از راستشه
        (5, 0, 5, 1, '<'),

        # عمودی: خانه وسط در سطر دوم کوچکتر از خانه زیرشه
        (6, 0, 6, 1, '>'),

        # عمودی: خانه وسط در سطر سوم بزرگتر از خانه پایین‌ترشه
        (3, 1, 4, 1, '>'),

        # ردیف دوم: خانه‌ی سمت چپ از خانه‌ی سمت راست بزرگ‌تره
        (4, 2, 4, 1, '>'),

        # عمودی: خانه سطر چهارم از زیرش بزرگتره
        (6, 1, 5, 1, '>'),

        # ردیف آخر: خانه قبل آخری باید بزرگ‌تر از آخری باشه
        (0, 2, 1, 2, '>'),
        (3, 2, 2, 2, '>'),
        (0, 3, 1, 3, '>'),
        (2, 4, 2, 3, '>'),
        (4, 3, 5, 3, '>'),
        (5, 3, 6, 3, '>'),
        (1, 4, 1, 5, '>'),
        (3, 4, 2, 4, '>'),
        (0, 5, 0, 6, '>'),
        (3, 5, 2, 5, '>'),
        (5, 5, 5, 4, '>'),
        (5, 6, 5, 5, '>'),
        (6, 5, 6, 6, '>')
    ]

    # --- اجرای حل ساده با استفاده از backtracking خالص ---
    print("حل با نسخه ساده (Backtracking خالص):")

    # ساخت یک نمونه از کلاس FutoshikiCSP برای حل نسخه ساده
    solver_simple = FutoshikiCSP(size, copy.deepcopy(grid), inequalities)

    # اجرای الگوریتم حل
    if solver_simple.simple_backtrack():
        # اگر حل شد، چاپ شبکه نهایی (ماتریس جواب)
        for row in solver_simple.grid:
            print(row)
    else:
        # اگر حل نشد:
        print("هیچ راه حلی یافت نشد!")

    # چاپ تعداد بازگشت‌ها برای بررسی عملکرد
    print(f"تعداد بازگشت‌ها: {solver_simple.backtracks}")

    # --- اجرای حل بهینه‌شده با استفاده از FC، AC-2، MRV و LCV ---
    print("\nحل با نسخه بهینه (با FC, AC-2, MRV, LCV):")

    # ساخت یک نمونه جدید از کلاس برای حل نسخه بهینه
    solver_opt = FutoshikiCSP(size, copy.deepcopy(grid), inequalities)

    # اجرای الگوریتم بهینه‌شده
    if solver_opt.optimized_backtrack():
        # اگر حل شد:
        for row in solver_opt.grid:
            print(row)
    else:
        print("هیچ راه حلی یافت نشد!")

    # چاپ تعداد بازگشت‌ها در روش بهینه برای مقایسه
    print(f"تعداد بازگشت‌ها: {solver_opt.backtracks}")

if __name__ == "__main__":
    main()
