import sys
from threading import Event

from utils import SATSolverResult, lit_to_dimacs, load_formula


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.values = [0] * num_lits

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess()
        self.build_occurrences()

    def preprocess(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses: list[list[int]] = []
        self.units = []
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.append(lits.pop())
            else:
                self.clauses.append(list(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int):
        """Сделать ℓ истинным на текущем уровне."""
        self.values[lit] = 1
        self.values[lit ^ 1] = -1
        self.trail.append(lit)

    def decide(self, lit: int):
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int):
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return
        values, trail = self.values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
        del trail[start:]
        del self.control[level:]
        self.propagated = start

    def save_model(self):
        values = self.values
        self.model = [
            lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
            ## а прописать в РИДМИ  что v от 1 начинается????
            ## изначально было от 1, щас на 0 переделал
            for v in range(self.num_vars)
        ]

    def build_occurrences(self):
        self.occurrences = [[] for _ in range(self.formula.num_lits)]
        for c in self.clauses:
            for lit in c:
                self.occurrences[lit].append(c)

    def build_watches(self):
        num_lits = self.formula.num_lits
        self.binary = [[] for _ in range(num_lits)]
        self.watches = [[] for _ in range(num_lits)]
        for c in self.clauses:
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])

    def propagate(self) -> bool:
        """
        UnitPropagate: распространить литералы trail[propagated:].
        Возвращает True, если найден конфликт (все литералы дизъюнкта ложны).
        """
        while self.propagated < len(self.trail):
            l = self.trail[self.propagated]
            self.propagated = self.propagated + 1

            # смотрим clause в которых есть еще не propogated переменная
            # так как они оттуда можем получить новые
            for c in self.occurrences[l ^ 1]:
                free_vars = 0
                free_var_id = 0
                flag = False
                for l2 in c:
                    # одна из переменных True
                    if self.values[l2] == 1:
                        # таким образом плевать на остальные
                        flag = True
                        break
                    if self.values[l2] == 0:
                        free_vars = free_vars + 1
                        free_var_id = l2
                if flag:
                    continue
                # дальше получаем что мы не нашли ни одно тру значение
                # все переменные False
                if free_vars == 0:
                    return True
                # одна свободная => ДОЛЖНА быть True
                if free_vars == 1:
                    self.assign(free_var_id)
                # откладываем на потом(не знаем сейчас)
                if free_vars >= 2:
                    continue
            # self.eliminate_pure_literals()
        return False

    def find_pure_literals(self) -> list[int]:
        seen = [False] * self.formula.num_lits

        for c in self.clauses:
            for l in c:
                seen[l] = True

        pure_literals = []
        for i in range(0, len(seen), 2):
            if seen[i] and not seen[i + 1]:
                pure_literals.append(i)

            if not seen[i] and seen[i + 1]:
                pure_literals.append(i + 1)

        return pure_literals

    def eliminate_pure_literals(self) -> None:
        for l in self.find_pure_literals():
            self.assign(l)

    def choose_literal(self) -> int | None:
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        for i, v in enumerate(self.values):
            if v == 0:
                return i
        return None

    def is_solved(self):
        for v in self.values:
            if v == 0:
                return False
        return True

    def solve_helper(self) -> SATSolverResult:

        if self.sigkill.is_set():  # TODO: your code should check this predicate frequently! If it is set, you should return
            return SATSolverResult.UNKNOWN
        l = self.choose_literal()
        # 1. смотрим если все подобрали
        if l is None:
            return SATSolverResult.SAT

        self.decide(l)

        if not self.propagate():
            # если нет конфликта и решили то ура гг победа
            if self.is_solved():
                return SATSolverResult.SAT
            # если нет конфликта и не решили то снова выбираем литерал
            if self.solve_helper() == SATSolverResult.SAT:
                return SATSolverResult.SAT

        # 2. если есть конфликт то бектрекаем и пробуем -l
        self.backtrack(self.level() - 1)
        self.decide(l ^ 1)

        if not self.propagate():
            # если нет конфликта и решили то ура гг победа
            if self.is_solved():
                return SATSolverResult.SAT
            # если нет конфликта и не решили то снова выбираем литерал
            if self.solve_helper() == SATSolverResult.SAT:
                return SATSolverResult.SAT

        # 3. если есть конфликт то бектрекаем и всё, возвращаемся обратно рекурсивно так как проебали для l и -l
        self.backtrack(self.level() - 1)
        return SATSolverResult.UNSAT

    def solve(self) -> SATSolverResult:
        # чекаем один раз изначальные юниты так как это БАЗА
        for l in self.units:
            if self.values[l ^ 1] == 1:
                return SATSolverResult.UNSAT
            self.assign(l)
        # пропагейтим их
        if self.propagate():
            return SATSolverResult.UNSAT
        # и смотрим если решили
        if self.is_solved():
            return SATSolverResult.SAT

        if self.has_empty_clause:
            return SATSolverResult.UNSAT
        if len(self.clauses) == 0:
            return SATSolverResult.SAT
        res = self.solve_helper()
        self.save_model()
        return res


if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
