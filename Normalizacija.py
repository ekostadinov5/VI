import sys
import math
from random import random
import bisect
from sys import maxsize as infinity
from math import log
from math import exp
from random import seed

"""
Дефинирање на класа за структурата на проблемот кој ќе го решаваме со пребарување.
Класата Problem е апстрактна класа од која правиме наследување за дефинирање на основните 
карактеристики на секој проблем што сакаме да го решиме
"""


class Problem:
    def __init__(self, initial, goal=None):
        self.initial = initial
        self.goal = goal

    def successor(self, state):
        """За дадена состојба, врати речник од парови {акција : состојба}
        достапни од оваа состојба. Ако има многу следбеници, употребете
        итератор кој би ги генерирал следбениците еден по еден, наместо да
        ги генерирате сите одеднаш.

        :param state: дадена состојба
        :return:  речник од парови {акција : состојба} достапни од оваа
                  состојба
        :rtype: dict
        """
        raise NotImplementedError

    def actions(self, state):
        """За дадена состојба state, врати листа од сите акции што може да
        се применат над таа состојба

        :param state: дадена состојба
        :return: листа на акции
        :rtype: list
        """
        return self.successor(state).keys()

    def result(self, state, action):
        """За дадена состојба state и акција action, врати ја состојбата
        што се добива со примена на акцијата над состојбата

        :param state: дадена состојба
        :param action: дадена акција
        :return: резултантна состојба
        """
        possible = self.successor(state)
        return possible[action]

    def goal_test(self, state):
        """Врати True ако state е целна состојба. Даденава имплементација
        на методот директно ја споредува state со self.goal, како што е
        специфицирана во конструкторот. Имплементирајте го овој метод ако
        проверката со една целна состојба self.goal не е доволна.

        :param state: дадена состојба
        :return: дали дадената состојба е целна состојба
        :rtype: bool
        """
        return state == self.goal

    def path_cost(self, c, state1, action, state2):
        """Врати ја цената на решавачкиот пат кој пристигнува во состојбата
        state2 од состојбата state1 преку акцијата action, претпоставувајќи
        дека цената на патот до состојбата state1 е c. Ако проблемот е таков
        што патот не е важен, оваа функција ќе ја разгледува само состојбата
        state2. Ако патот е важен, ќе ја разгледува цената c и можеби и
        state1 и action. Даденава имплементација му доделува цена 1 на секој
        чекор од патот.

        :param c: цена на патот до состојбата state1
        :param state1: дадена моментална состојба
        :param action: акција која треба да се изврши
        :param state2: состојба во која треба да се стигне
        :return: цена на патот по извршување на акцијата
        :rtype: float
        """
        return c + 1

    def value(self):
        """За проблеми на оптимизација, секоја состојба си има вредност. 
        Hill-climbing и сличните алгоритми се обидуваат да ја максимизираат
        оваа вредност.

        :return: вредност на состојба
        :rtype: float
        """
        raise NotImplementedError


"""
Дефинирање на класата за структурата на јазел од пребарување.
Класата Node не се наследува
"""


class Node:
    def __init__(self, state, parent=None, action=None, path_cost=0):
        """Креирај јазол од пребарувачкото дрво, добиен од parent со примена
        на акцијата action

        :param state: моментална состојба (current state)
        :param parent: родителска состојба (parent state)
        :param action: акција (action)
        :param path_cost: цена на патот (path cost)
        """
        self.state = state
        self.parent = parent
        self.action = action
        self.path_cost = path_cost
        self.depth = 0  # search depth
        if parent:
            self.depth = parent.depth + 1

    def __repr__(self):
        return "<Node %s>" % (self.state,)

    def __lt__(self, node):
        return self.state < node.state

    def expand(self, problem):
        """Излистај ги јазлите достапни во еден чекор од овој јазол.

        :param problem: даден проблем
        :return: листа на достапни јазли во еден чекор
        :rtype: list(Node)
        """

        return [self.child_node(problem, action)
                for action in problem.actions(self.state)]

    def child_node(self, problem, action):
        """Дете јазел

        :param problem: даден проблем
        :param action: дадена акција
        :return: достапен јазел според дадената акција
        :rtype: Node
        """
        next_state = problem.result(self.state, action)
        return Node(next_state, self, action,
                    problem.path_cost(self.path_cost, self.state,
                                      action, next_state))

    def solution(self):
        """Врати ја секвенцата од акции за да се стигне од коренот до овој јазол.

        :return: секвенцата од акции
        :rtype: list
        """
        return [node.action for node in self.path()[1:]]

    def solve(self):
        """Врати ја секвенцата од состојби за да се стигне од коренот до овој јазол.

        :return: листа од состојби
        :rtype: list
        """
        return [node.state for node in self.path()[0:]]

    def path(self):
        """Врати ја листата од јазли што го формираат патот од коренот до овој јазол.

        :return: листа од јазли од патот
        :rtype: list(Node)
        """
        x, result = self, []
        while x:
            result.append(x)
            x = x.parent
        result.reverse()
        return result

    """Сакаме редицата од јазли кај breadth_first_search или 
    astar_search да не содржи состојби - дупликати, па јазлите што
    содржат иста состојба ги третираме како исти. [Проблем: ова може
    да не биде пожелно во други ситуации.]"""

    def __eq__(self, other):
        return isinstance(other, Node) and self.state == other.state

    def __hash__(self):
        return hash(self.state)


"""
Дефинирање на помошни структури за чување на листата на генерирани, но непроверени јазли
"""


class Queue:
    """Queue е апстрактна класа / интерфејс. Постојат 3 типа:
        Stack(): Last In First Out Queue (стек).
        FIFOQueue(): First In First Out Queue (редица).
        PriorityQueue(order, f): Queue во сортиран редослед (подразбирливо,од најмалиот кон
                                 најголемиот јазол).
    """

    def __init__(self):
        raise NotImplementedError

    def append(self, item):
        """Додади го елементот item во редицата

        :param item: даден елемент
        :return: None
        """
        raise NotImplementedError

    def extend(self, items):
        """Додади ги елементите items во редицата

        :param items: дадени елементи
        :return: None
        """
        raise NotImplementedError

    def pop(self):
        """Врати го првиот елемент од редицата

        :return: прв елемент
        """
        raise NotImplementedError

    def __len__(self):
        """Врати го бројот на елементи во редицата

        :return: број на елементи во редицата
        :rtype: int
        """
        raise NotImplementedError

    def __contains__(self, item):
        """Проверка дали редицата го содржи елементот item

        :param item: даден елемент
        :return: дали queue го содржи item
        :rtype: bool
        """
        raise NotImplementedError


class Stack(Queue):
    """Last-In-First-Out Queue."""

    def __init__(self):
        self.data = []

    def append(self, item):
        self.data.append(item)

    def extend(self, items):
        self.data.extend(items)

    def pop(self):
        return self.data.pop()

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return item in self.data


class FIFOQueue(Queue):
    """First-In-First-Out Queue."""

    def __init__(self):
        self.data = []

    def append(self, item):
        self.data.append(item)

    def extend(self, items):
        self.data.extend(items)

    def pop(self):
        return self.data.pop(0)

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return item in self.data


class PriorityQueue(Queue):
    """Редица во која прво се враќа минималниот (или максималниот) елемент
    (како што е определено со f и order). Оваа структура се користи кај
    информирано пребарување"""
    """"""

    def __init__(self, order=min, f=lambda x: x):
        """
        :param order: функција за подредување, ако order е min, се враќа елементот
                      со минимална f(x); ако order е max, тогаш се враќа елементот
                      со максимална f(x).
        :param f: функција f(x)
        """
        assert order in [min, max]
        self.data = []
        self.order = order
        self.f = f

    def append(self, item):
        bisect.insort_right(self.data, (self.f(item), item))

    def extend(self, items):
        for item in items:
            bisect.insort_right(self.data, (self.f(item), item))

    def pop(self):
        if self.order == min:
            return self.data.pop(0)[1]
        return self.data.pop()[1]

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return any(item == pair[1] for pair in self.data)

    def __getitem__(self, key):
        for _, item in self.data:
            if item == key:
                return item

    def __delitem__(self, key):
        for i, (value, item) in enumerate(self.data):
            if item == key:
                self.data.pop(i)


"""
Неинформирано пребарување во рамки на дрво.
Во рамки на дрвото не разрешуваме јамки.
"""


def tree_search(problem, fringe):
    """ Пребарувај низ следбениците на даден проблем за да најдеш цел.

    :param problem: даден проблем
    :param fringe:  празна редица (queue)
    :return: Node
    """
    fringe.append(Node(problem.initial))
    while fringe:
        node = fringe.pop()
        #print(node.state)
        if problem.goal_test(node.state):
            return node
        fringe.extend(node.expand(problem))
    return None


def breadth_first_tree_search(problem):
    """Експандирај го прво најплиткиот јазол во пребарувачкото дрво.

    :param problem: даден проблем
    :return: Node
    """
    return tree_search(problem, FIFOQueue())


def depth_first_tree_search(problem):
    """Експандирај го прво најдлабокиот јазол во пребарувачкото дрво.

    :param problem:даден проблем
    :return: Node
    """
    return tree_search(problem, Stack())


"""
Неинформирано пребарување во рамки на граф
Основната разлика е во тоа што овде не дозволуваме јамки, 
т.е. повторување на состојби
"""


def graph_search(problem, fringe):
    """Пребарувај низ следбениците на даден проблем за да најдеш цел.
     Ако до дадена состојба стигнат два пата, употреби го најдобриот пат.

    :param problem: даден проблем
    :param fringe: празна редица (queue)
    :return: Node
    """
    closed = set()
    fringe.append(Node(problem.initial))
    while fringe:
        node = fringe.pop()
        if problem.goal_test(node.state):
            return node
        if node.state not in closed:
            closed.add(node.state)
            fringe.extend(node.expand(problem))
    return None


def breadth_first_graph_search(problem):
    """Експандирај го прво најплиткиот јазол во пребарувачкиот граф.

    :param problem: даден проблем
    :return: Node
    """
    return graph_search(problem, FIFOQueue())


def depth_first_graph_search(problem):
    """Експандирај го прво најдлабокиот јазол во пребарувачкиот граф.

    :param problem: даден проблем
    :return: Node
    """
    return graph_search(problem, Stack())


def depth_limited_search(problem, limit=50):
    def recursive_dls(node, problem, limit):
        """Помошна функција за depth limited"""
        cutoff_occurred = False
        if problem.goal_test(node.state):
            return node
        elif node.depth == limit:
            return 'cutoff'
        else:
            for successor in node.expand(problem):
                result = recursive_dls(successor, problem, limit)
                if result == 'cutoff':
                    cutoff_occurred = True
                elif result is not None:
                    return result
        if cutoff_occurred:
            return 'cutoff'
        return None

    return recursive_dls(Node(problem.initial), problem, limit)


def iterative_deepening_search(problem):
    for depth in range(sys.maxsize):
        result = depth_limited_search(problem, depth)
        if result is not 'cutoff':
            return result


def uniform_cost_search(problem):
    """Експандирај го прво јазолот со најниска цена во пребарувачкиот граф."""
    return graph_search(problem, PriorityQueue(min, lambda a: a.path_cost))


"""
Информирано пребарување во рамки на граф
"""


def memoize(fn, slot=None):
    """ Запамети ја пресметаната вредност за која била листа од
    аргументи. Ако е специфициран slot, зачувај го резултатот во
    тој slot на првиот аргумент. Ако slot е None, зачувај ги
    резултатите во речник.

    :param fn: зададена функција
    :param slot: име на атрибут во кој се чуваат резултатите од функцијата
    :return: функција со модификација за зачувување на резултатите
    """
    if slot:
        def memoized_fn(obj, *args):
            if hasattr(obj, slot):
                return getattr(obj, slot)
            else:
                val = fn(obj, *args)
                setattr(obj, slot, val)
                return val
    else:
        def memoized_fn(*args):
            if args not in memoized_fn.cache:
                memoized_fn.cache[args] = fn(*args)
            return memoized_fn.cache[args]

        memoized_fn.cache = {}
    return memoized_fn


def best_first_graph_search(problem, f):
    """Пребарувај низ следбениците на даден проблем за да најдеш цел. Користи
     функција за евалуација за да се одлучи кој е сосед најмногу ветува и
     потоа да се истражи. Ако до дадена состојба стигнат два пата, употреби
     го најдобриот пат.

    :param problem: даден проблем
    :param f: дадена функција за евристика
    :return: Node or None
    """
    f = memoize(f, 'f')
    node = Node(problem.initial)
    if problem.goal_test(node.state):
        return node
    frontier = PriorityQueue(min, f)
    frontier.append(node)
    explored = set()
    while frontier:
        node = frontier.pop()
        if problem.goal_test(node.state):
            return node
        explored.add(node.state)
        for child in node.expand(problem):
            if child.state not in explored and child not in frontier:
                frontier.append(child)
            elif child in frontier:
                incumbent = frontier[child]
                if f(child) < f(incumbent):
                    del frontier[incumbent]
                    frontier.append(child)
    return None


def greedy_best_first_graph_search(problem, h=None):
    """ Greedy best-first пребарување се остварува ако се специфицира дека f(n) = h(n).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')
    return best_first_graph_search(problem, h)


def astar_search(problem, h=None):
    """ A* пребарување е best-first graph пребарување каде f(n) = g(n) + h(n).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')
    return best_first_graph_search(problem, lambda n: n.path_cost + h(n))


def recursive_best_first_search(problem, h=None):
    """Recursive best first search - ја ограничува рекурзијата
    преку следење на f-вредноста на најдобриот алтернативен пат
    од било кој јазел предок (еден чекор гледање нанапред).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')

    def RBFS(problem, node, flimit):
        if problem.goal_test(node.state):
            return node, 0  # (втората вредност е неважна)
        successors = node.expand(problem)
        if len(successors) == 0:
            return None, infinity
        for s in successors:
            s.f = max(s.path_cost + h(s), node.f)
        while True:
            # Подреди ги според најниската f вредност
            successors.sort(key=lambda x: x.f)
            best = successors[0]
            if best.f > flimit:
                return None, best.f
            if len(successors) > 1:
                alternative = successors[1].f
            else:
                alternative = infinity
            result, best.f = RBFS(problem, best, min(flimit, alternative))
            if result is not None:
                return result, best.f

    node = Node(problem.initial)
    node.f = h(node)
    result, bestf = RBFS(problem, node, infinity)
    return result


"""
Пребарување низ проблем дефиниран како конечен граф
"""


def distance(a, b):
    """Растојание помеѓу две (x, y) точки."""
    return math.hypot((a[0] - b[0]), (a[1] - b[1]))


class Graph:
    def __init__(self, dictionary=None, directed=True):
        self.dict = dictionary or {}
        self.directed = directed
        if not directed:
            self.make_undirected()
        else:
            # додади празен речник за линковите на оние јазли кои немаат
            # насочени врски и не се дадени како клучеви во речникот
            nodes_no_edges = list({y for x in self.dict.values()
                                   for y in x if y not in self.dict})
            for node in nodes_no_edges:
                self.dict[node] = {}

    def make_undirected(self):
        """Ориентираниот граф претвори го во неориентиран со додавање
        на симетричните ребра."""
        for a in list(self.dict.keys()):
            for (b, dist) in self.dict[a].items():
                self.connect1(b, a, dist)

    def connect(self, node_a, node_b, distance_val=1):
        """Додади ребро од A до B со дадено растојание, а додади го и
        обратното ребро (од B до A) ако графот е неориентиран."""
        self.connect1(node_a, node_b, distance_val)
        if not self.directed:
            self.connect1(node_b, node_a, distance_val)

    def connect1(self, node_a, node_b, distance_val):
        """Додади ребро од A до B со дадено растојание, но само во
        едната насока."""
        self.dict.setdefault(node_a, {})[node_b] = distance_val

    def get(self, a, b=None):
        """Врати растојание придружено на ребро или пак врати речник
        чии елементи се од обликот {јазол : растојание}.
        .get(a,b) го враќа растојанието или пак враќа None
        .get(a) враќа речник со елементи од обликот {јазол : растојание},
            кој може да биде и празен – {}."""
        links = self.dict.get(a)
        if b is None:
            return links
        else:
            return links.get(b)

    def nodes(self):
        """Врати листа од јазлите во графот."""
        return list(self.dict.keys())


def UndirectedGraph(dictionary=None):
    """Изгради Graph во кој што секое ребро (вклучувајќи ги и идните
    ребра) е двонасочно."""
    return Graph(dictionary=dictionary, directed=False)


def RandomGraph(nodes=list(range(10)), min_links=2, width=400, height=300,
                curvature=lambda: random.uniform(1.1, 1.5)):
    """Construct a random graph, with the specified nodes, and random links.
    The nodes are laid out randomly on a (width x height) rectangle.
    Then each node is connected to the min_links nearest neighbors.
    Because inverse links are added, some nodes will have more connections.
    The distance between nodes is the hypotenuse times curvature(),
    where curvature() defaults to a random number between 1.1 and 1.5."""
    g = UndirectedGraph()
    g.locations = {}
    # Build the cities
    for node in nodes:
        g.locations[node] = (random.randrange(width), random.randrange(height))
    # Build roads from each city to at least min_links nearest neighbors.
    for i in range(min_links):
        for node in nodes:
            if len(g.get(node)) < min_links:
                here = g.locations[node]

                def distance_to_node(n):
                    if n is node or g.get(node, n):
                        return math.inf
                    return distance(g.locations[n], here)

                neighbor = nodes.index(min(nodes, key=distance_to_node))
                d = distance(g.locations[neighbor], here) * curvature()
                g.connect(node, neighbor, int(d))
    return g


class GraphProblem(Problem):
    """Проблем на пребарување на граф од еден до друг јазол."""

    def __init__(self, initial, goal, graph):
        super().__init__(initial, goal)
        self.graph = graph

    def actions(self, state):
        """Акциите кај јазол во граф се едноставно - неговите соседи."""
        return list(self.graph.get(state).keys())

    def result(self, state, action):
        """Резултат на одењето кон сосед е самиот тој сосед."""
        return action

    def path_cost(self, c, state1, action, state2):
        return c + (self.graph.get(state1, state2) or math.inf)

    def h(self, node):
        """Функцијата h е праволиниско растојание од состојбата зачувана
        во тековниот јазол до целната состојба."""
        locs = getattr(self.graph, 'locations', None)
        if locs:
            return int(distance(locs[node.state], locs[self.goal]))
        else:
            return math.inf



"""
DRVA NA ODLUKA
"""

def unique_counts(rows):
    """Креирај броење на можни резултати (последната колона
    во секоја редица е класата)

    :param rows: dataset
    :type rows: list
    :return: dictionary of possible classes as keys and count
             as values
    :rtype: dict
    """
    results = {}
    for row in rows:
        # Клацата е последната колона
        r = row[len(row) - 1]
        if r not in results:
            results[r] = 0
        results[r] += 1
    return results


def gini_impurity(rows):
    """Probability that a randomly placed item will
    be in the wrong category

    :param rows: dataset
    :type rows: list
    :return: Gini impurity
    :rtype: float
    """
    total = len(rows)
    counts = unique_counts(rows)
    imp = 0
    for k1 in counts:
        p1 = float(counts[k1]) / total
        for k2 in counts:
            if k1 == k2:
                continue
            p2 = float(counts[k2]) / total
            imp += p1 * p2
    return imp


def entropy(rows):
    """Ентропијата е сума од p(x)log(p(x)) за сите
    можни резултати

    :param rows: податочно множество
    :type rows: list
    :return: вредност за ентропијата
    :rtype: float
    """
    log2 = lambda x: log(x) / log(2)
    results = unique_counts(rows)
    # Пресметка на ентропијата
    ent = 0.0
    for r in results.keys():
        p = float(results[r]) / len(rows)
        ent = ent - p * log2(p)
    return ent


class DecisionNode:
    def __init__(self, col=-1, value=None, results=None, tb=None, fb=None):
        """
        :param col: индексот на колоната (атрибутот) од тренинг множеството
                    која се претставува со оваа инстанца т.е. со овој јазол
        :type col: int
        :param value: вредноста на јазолот според кој се дели дрвото
        :param results: резултати за тековната гранка, вредност (различна
                        од None) само кај јазлите-листови во кои се донесува
                        одлуката.
        :type results: dict
        :param tb: гранка која се дели од тековниот јазол кога вредноста е
                   еднаква на value
        :type tb: DecisionNode
        :param fb: гранка која се дели од тековниот јазол кога вредноста е
                   различна од value
        :type fb: DecisionNode
        """
        self.col = col
        self.value = value
        self.results = results
        self.tb = tb
        self.fb = fb


def compare_numerical(row, column, value):
    """Споредба на вредноста од редицата на посакуваната колона со
    зададена нумеричка вредност

    :param row: дадена редица во податочното множество
    :type row: list
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во согласност со кој се прави
                  поделбата во дрвото
    :type value: int or float
    :return: True ако редицата >= value, инаку False
    :rtype: bool
    """
    return row[column] >= value


def compare_nominal(row, column, value):
    """Споредба на вредноста од редицата на посакуваната колона со
    зададена номинална вредност

    :param row: дадена редица во податочното множество
    :type row: list
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во согласност со кој се прави
                  поделбата во дрвото
    :type value: str
    :return: True ако редицата == value, инаку False
    :rtype: bool
    """
    return row[column] == value


def divide_set(rows, column, value):
    """Поделба на множеството според одредена колона. Може да се справи
    со нумерички или номинални вредности.

    :param rows: тренирачко множество
    :type rows: list(list)
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во зависност со кој се прави поделбата
                  во дрвото за конкретната гранка
    :type value: int or float or str
    :return: поделени подмножества
    :rtype: list, list
    """
    # Направи функција која ни кажува дали редицата е во
    # првата група (True) или втората група (False)
    if isinstance(value, int) or isinstance(value, float):
        # ако вредноста за споредба е од тип int или float
        split_function = compare_numerical
    else:
        # ако вредноста за споредба е од друг тип (string)
        split_function = compare_nominal

    # Подели ги редиците во две подмножества и врати ги
    # за секој ред за кој split_function враќа True
    set1 = [row for row in rows if
            split_function(row, column, value)]
    # за секој ред за кој split_function враќа False
    set2 = [row for row in rows if
            not split_function(row, column, value)]
    return set1, set2


def build_tree(rows, scoref=entropy):
    if len(rows) == 0:
        return DecisionNode()
    current_score = scoref(rows)

    # променливи со кои следиме кој критериум е најдобар
    best_gain = 0.0
    best_criteria = None
    best_sets = None

    column_count = len(rows[0]) - 1
    for col in range(0, column_count):
        # за секоја колона (col се движи во интервалот од 0 до
        # column_count - 1)
        # Следниов циклус е за генерирање на речник од различни
        # вредности во оваа колона
        column_values = {}
        for row in rows:
            column_values[row[col]] = 1
        # за секоја редица се зема вредноста во оваа колона и се
        # поставува како клуч во column_values
        for value in column_values.keys():
            (set1, set2) = divide_set(rows, col, value)

            # Информациона добивка
            p = float(len(set1)) / len(rows)
            gain = current_score - p * scoref(set1) - (1 - p) * scoref(set2)
            if gain > best_gain and len(set1) > 0 and len(set2) > 0:
                best_gain = gain
                best_criteria = (col, value)
                best_sets = (set1, set2)

    # Креирај ги подгранките
    if best_gain > 0:
        true_branch = build_tree(best_sets[0], scoref)
        false_branch = build_tree(best_sets[1], scoref)
        return DecisionNode(col=best_criteria[0], value=best_criteria[1],
                            tb=true_branch, fb=false_branch)
    else:
        return DecisionNode(results=unique_counts(rows))


def print_tree(tree, indent=''):
    # Дали е ова лист јазел?
    if tree.results:
        print(str(tree.results))
    else:
        # Се печати условот
        print(str(tree.col) + ':' + str(tree.value) + '? ')
        # Се печатат True гранките, па False гранките
        print(indent + 'T->', end='')
        print_tree(tree.tb, indent + '  ')
        print(indent + 'F->', end='')
        print_tree(tree.fb, indent + '  ')


def classify(observation, tree):
    if tree.results:
        return tree.results
    else:
        value = observation[tree.col]
        if isinstance(value, int) or isinstance(value, float):
            compare = compare_numerical
        else:
            compare = compare_nominal

        if compare(observation, tree.col, tree.value):
            branch = tree.tb
        else:
            branch = tree.fb

        return classify(observation, branch)



"""
NEVRONSKI MREZHI
"""

# Иницијализација на мрежа
# Ставете фиксни тежини од 0.5 на code.finki.ukim.mk ако постои проблем со random()
def initialize_network(n_inputs, n_hidden, n_outputs):
    """Изградба на мрежата и иницијализација на тежините

    :param n_inputs: број на неврони во влезниот слој
    :type n_inputs: int
    :param n_hidden: број на неврони во скриениот слој
    :type n_hidden: int
    :param n_outputs: број на неврони во излезниот слој
                      (број на класи)
    :type n_outputs: int
    :return: мрежата како листа на слоеви, каде што секој
             слој е речник со клуч 'weights' и нивните вредности
    :rtype: list(list(dict(str, list)))
    """
    network = list()
    hidden_layer = [{'weights': [random() for _ in range(n_inputs + 1)]}
                    for _ in range(n_hidden)]
    network.append(hidden_layer)
    output_layer = [{'weights': [random() for _ in range(n_hidden + 1)]}
                    for _ in range(n_outputs)]
    network.append(output_layer)
    return network


def neuron_calculate(weights, inputs):
    """Пресметување на вредноста за активација на неврон

    :param weights: даден вектор (листа) на тежини
    :type weights: list(float)
    :param inputs: даден вектор (листа) на влезови
    :type inputs: list(float)
    :return: пресметка на невронот
    :rtype: float
    """
    activation = weights[-1]
    for i in range(len(weights) - 1):
        activation += weights[i] * inputs[i]
    return activation


def sigmoid_activation(activation):
    """Sigmoid активациска функција

    :param activation: вредност за активациската функција
    :type activation: float
    :return: вредност добиена од примена на активациската
             функција
    :rtype: float
    """
    return 1.0 / (1.0 + exp(-activation))


def forward_propagate(network, row):
    """Пропагирање нанапред на влезот кон излезот на мрежата

    :param network: дадената мрежа
    :param row: моменталната податочна инстаца
    :return: листа на излезите од последниот слој
    """
    inputs = row
    for layer in network:
        new_inputs = []
        for neuron in layer:
            activation = neuron_calculate(neuron['weights'], inputs)
            neuron['output'] = sigmoid_activation(activation)
            new_inputs.append(neuron['output'])
        inputs = new_inputs
    return inputs


def sigmoid_activation_derivative(output):
    """Пресметување на изводот на излезот од невронот

    :param output: излезни вредности
    :return: вредност на изводот
    """
    return output * (1.0 - output)


def backward_propagate_error(network, expected):
    """Пропагирање на грешката наназад и сочувување во невроните

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param expected: очекувани вредности за излезот
    :type expected: list(int)
    :return: None
    """
    for i in reversed(range(len(network))):
        layer = network[i]
        errors = list()
        if i != len(network) - 1:
            for j in range(len(layer)):
                error = 0.0
                for neuron in network[i + 1]:
                    error += (neuron['weights'][j] * neuron['delta'])
                errors.append(error)
        else:
            for j in range(len(layer)):
                neuron = layer[j]
                errors.append(expected[j] - neuron['output'])
        for j in range(len(layer)):
            neuron = layer[j]
            neuron['delta'] = errors[j] * sigmoid_activation_derivative(neuron['output'])


def update_weights(network, row, l_rate):
    """Ажурирање на тежините на мрежата со грешката

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една инстанца на податоци
    :type row: list
    :param l_rate: рата на учење
    :type l_rate: float
    :return: None
    """
    for i in range(len(network)):
        inputs = row[:-1]
        if i != 0:
            inputs = [neuron['output'] for neuron in network[i - 1]]
        for neuron in network[i]:
            for j in range(len(inputs)):
                neuron['weights'][j] += l_rate * neuron['delta'] * inputs[j]
            neuron['weights'][-1] += l_rate * neuron['delta']


def train_network(network, train, l_rate, n_epoch, n_outputs, verbose=True):
    """Тренирање на мрежата за фиксен број на епохи

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param train: тренирачко множество
    :type train: list
    :param l_rate: рата на учење
    :type l_rate: float
    :param n_epoch: број на епохи
    :type n_epoch: int
    :param n_outputs: број на неврони (класи) во излезниот слој
    :type n_outputs: int
    :param verbose: True за принтање на лог, инаку False
    :type: verbose: bool
    :return: None
    """
    for epoch in range(n_epoch):
        sum_error = 0
        for row in train:
            outputs = forward_propagate(network, row)
            expected = [0] * n_outputs
            expected[row[-1]] = 1
            sum_error += sum([(expected[i] - outputs[i]) ** 2 for i in range(len(expected))])
            backward_propagate_error(network, expected)
            update_weights(network, row, l_rate)
        if verbose:
            print('>epoch=%d, lrate=%.3f, error=%.3f' % (epoch, l_rate, sum_error))


def predict(network, row):
    """Направи предвидување

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една податочна инстанца
    :type row: list
    :return: предвидени класи
    """
    outputs = forward_propagate(network, row)
    return outputs.index(max(outputs))



seed(1)

training_data = [
    [3.6216, 8.6661, -2.8073, -0.44699, 0],
    [4.5459, 8.1674, -2.4586, -1.4621, 0],
    [3.866, -2.6383, 1.9242, 0.10645, 0],
    [3.4566, 9.5228, -4.0112, -3.5944, 0],
    [0.32924, -4.4552, 4.5718, -0.9888, 0],
    [4.3684, 9.6718, -3.9606, -3.1625, 0],
    [3.5912, 3.0129, 0.72888, 0.56421, 0],
    [2.0922, -6.81, 8.4636, -0.60216, 0],
    [3.2032, 5.7588, -0.75345, -0.61251, 0],
    [1.5356, 9.1772, -2.2718, -0.73535, 0],
    [1.2247, 8.7779, -2.2135, -0.80647, 0],
    [3.9899, -2.7066, 2.3946, 0.86291, 0],
    [1.8993, 7.6625, 0.15394, -3.1108, 0],
    [-1.5768, 10.843, 2.5462, -2.9362, 0],
    [3.404, 8.7261, -2.9915, -0.57242, 0],
    [4.6765, -3.3895, 3.4896, 1.4771, 0],
    [2.6719, 3.0646, 0.37158, 0.58619, 0],
    [0.80355, 2.8473, 4.3439, 0.6017, 0],
    [1.4479, -4.8794, 8.3428, -2.1086, 0],
    [5.2423, 11.0272, -4.353, -4.1013, 0],
    [5.7867, 7.8902, -2.6196, -0.48708, 0],
    [0.3292, -4.4552, 4.5718, -0.9888, 0],
    [3.9362, 10.1622, -3.8235, -4.0172, 0],
    [0.93584, 8.8855, -1.6831, -1.6599, 0],
    [4.4338, 9.887, -4.6795, -3.7483, 0],
    [0.7057, -5.4981, 8.3368, -2.8715, 0],
    [1.1432, -3.7413, 5.5777, -0.63578, 0],
    [-0.38214, 8.3909, 2.1624, -3.7405, 0],
    [6.5633, 9.8187, -4.4113, -3.2258, 0],
    [4.8906, -3.3584, 3.4202, 1.0905, 0],
    [-0.24811, -0.17797, 4.9068, 0.15429, 0],
    [1.4884, 3.6274, 3.308, 0.48921, 0],
    [4.2969, 7.617, -2.3874, -0.96164, 0],
    [-0.96511, 9.4111, 1.7305, -4.8629, 0],
    [-1.6162, 0.80908, 8.1628, 0.60817, 0],
    [2.4391, 6.4417, -0.80743, -0.69139, 0],
    [2.6881, 6.0195, -0.46641, -0.69268, 0],
    [3.6289, 0.81322, 1.6277, 0.77627, 0],
    [4.5679, 3.1929, -2.1055, 0.29653, 0],
    [3.4805, 9.7008, -3.7541, -3.4379, 0],
    [4.1711, 8.722, -3.0224, -0.59699, 0],
    [-0.2062, 9.2207, -3.7044, -6.8103, 0],
    [-0.0068919, 9.2931, -0.41243, -1.9638, 0],
    [0.96441, 5.8395, 2.3235, 0.066365, 0],
    [2.8561, 6.9176, -0.79372, 0.48403, 0],
    [-0.7869, 9.5663, -3.7867, -7.5034, 0],
    [2.0843, 6.6258, 0.48382, -2.2134, 0],
    [-0.7869, 9.5663, -3.7867, -7.5034, 0],
    [3.9102, 6.065, -2.4534, -0.68234, 0],
    [1.6349, 3.286, 2.8753, 0.087054, 0],
    [4.3239, -4.8835, 3.4356, -0.5776, 0],
    [5.262, 3.9834, -1.5572, 1.0103, 0],
    [3.1452, 5.825, -0.51439, -1.4944, 0],
    [2.549, 6.1499, -1.1605, -1.2371, 0],
    [4.9264, 5.496, -2.4774, -0.50648, 0],
    [4.8265, 0.80287, 1.6371, 1.1875, 0],
    [2.5635, 6.7769, -0.61979, 0.38576, 0],
    [5.807, 5.0097, -2.2384, 0.43878, 0],
    [3.1377, -4.1096, 4.5701, 0.98963, 0],
    [-0.78289, 11.3603, -0.37644, -7.0495, 0],
    [-1.3971, 3.3191, -1.3927, -1.9948, 1],
    [0.39012, -0.14279, -0.031994, 0.35084, 1],
    [-1.6677, -7.1535, 7.8929, 0.96765, 1],
    [-3.8483, -12.8047, 15.6824, -1.281, 1],
    [-3.5681, -8.213, 10.083, 0.96765, 1],
    [-2.2804, -0.30626, 1.3347, 1.3763, 1],
    [-1.7582, 2.7397, -2.5323, -2.234, 1],
    [-0.89409, 3.1991, -1.8219, -2.9452, 1],
    [0.3434, 0.12415, -0.28733, 0.14654, 1],
    [-0.9854, -6.661, 5.8245, 0.5461, 1],
    [-2.4115, -9.1359, 9.3444, -0.65259, 1],
    [-1.5252, -6.2534, 5.3524, 0.59912, 1],
    [-0.61442, -0.091058, -0.31818, 0.50214, 1],
    [-0.36506, 2.8928, -3.6461, -3.0603, 1],
    [-5.9034, 6.5679, 0.67661, -6.6797, 1],
    [-1.8215, 2.7521, -0.72261, -2.353, 1],
    [-0.77461, -1.8768, 2.4023, 1.1319, 1],
    [-1.8187, -9.0366, 9.0162, -0.12243, 1],
    [-3.5801, -12.9309, 13.1779, -2.5677, 1],
    [-1.8219, -6.8824, 5.4681, 0.057313, 1],
    [-0.3481, -0.38696, -0.47841, 0.62627, 1],
    [0.47368, 3.3605, -4.5064, -4.0431, 1],
    [-3.4083, 4.8587, -0.76888, -4.8668, 1],
    [-1.6662, -0.30005, 1.4238, 0.024986, 1],
    [-2.0962, -7.1059, 6.6188, -0.33708, 1],
    [-2.6685, -10.4519, 9.1139, -1.7323, 1],
    [-0.47465, -4.3496, 1.9901, 0.7517, 1],
    [1.0552, 1.1857, -2.6411, 0.11033, 1],
    [1.1644, 3.8095, -4.9408, -4.0909, 1],
    [-4.4779, 7.3708, -0.31218, -6.7754, 1],
    [-2.7338, 0.45523, 2.4391, 0.21766, 1],
    [-2.286, -5.4484, 5.8039, 0.88231, 1],
    [-1.6244, -6.3444, 4.6575, 0.16981, 1],
    [0.50813, 0.47799, -1.9804, 0.57714, 1],
    [1.6408, 4.2503, -4.9023, -2.6621, 1],
    [0.81583, 4.84, -5.2613, -6.0823, 1],
    [-5.4901, 9.1048, -0.38758, -5.9763, 1],
    [-3.2238, 2.7935, 0.32274, -0.86078, 1],
    [-2.0631, -1.5147, 1.219, 0.44524, 1],
    [-0.91318, -2.0113, -0.19565, 0.066365, 1],
    [0.6005, 1.9327, -3.2888, -0.32415, 1],
    [0.91315, 3.3377, -4.0557, -1.6741, 1],
    [-0.28015, 3.0729, -3.3857, -2.9155, 1],
    [-3.6085, 3.3253, -0.51954, -3.5737, 1],
    [-6.2003, 8.6806, 0.0091344, -3.703, 1],
    [-4.2932, 3.3419, 0.77258, -0.99785, 1],
    [-3.0265, -0.062088, 0.68604, -0.055186, 1],
    [-1.7015, -0.010356, -0.99337, -0.53104, 1],
    [-0.64326, 2.4748, -2.9452, -1.0276, 1],
    [-0.86339, 1.9348, -2.3729, -1.0897, 1],
    [-2.0659, 1.0512, -0.46298, -1.0974, 1],
    [-2.1333, 1.5685, -0.084261, -1.7453, 1],
    [-1.2568, -1.4733, 2.8718, 0.44653, 1],
    [-3.1128, -6.841, 10.7402, -1.0172, 1],
    [-4.8554, -5.9037, 10.9818, -0.82199, 1],
    [-2.588, 3.8654, -0.3336, -1.2797, 1],
    [0.24394, 1.4733, -1.4192, -0.58535, 1],
    [-1.5322, -5.0966, 6.6779, 0.17498, 1],
    [-4.0025, -13.4979, 17.6772, -3.3202, 1],
    [-4.0173, -8.3123, 12.4547, -1.4375, 1]
]

testing_data = [
    [2.888, 0.44696, 4.5907, -0.24398, 0],
    [0.49665, 5.527, 1.7785, -0.47156, 0],
    [4.2586, 11.2962, -4.0943, -4.3457, 0],
    [1.7939, -1.1174, 1.5454, -0.26079, 0],
    [5.4021, 3.1039, -1.1536, 1.5651, 0],
    [2.5367, 2.599, 2.0938, 0.20085, 0],
    [4.6054, -4.0765, 2.7587, 0.31981, 0],
    [-1.979, 3.2301, -1.3575, -2.5819, 1],
    [-0.4294, -0.14693, 0.044265, -0.15605, 1],
    [-2.234, -7.0314, 7.4936, 0.61334, 1],
    [-4.211, -12.4736, 14.9704, -1.3884, 1],
    [-3.8073, -8.0971, 10.1772, 0.65084, 1],
    [-2.5912, -0.10554, 1.2798, 1.0414, 1],
    [-2.2482, 3.0915, -2.3969, -2.6711, 1]
]


#x_norm[i, j] = (x[i, j] - min) / (max - min)
def x_norm(x, mini, maxi):
    return (x - mini) / (maxi - mini)



# f-ja za normalizacija
def minMaxNrom(training_data, testing_data):

    new_data = [[] for row in training_data]
    new_testing_data = [[] for row in testing_data]

    for i in range(len(training_data[0]) - 1):
        maxValue = max([val[i] for val in training_data])
        minValue = min([val[i] for val in training_data])

        for j in range(len(training_data)):
            new_data[j].append(x_norm(training_data[j][i], minValue, maxValue))

        for j in range(len(testing_data)):
            new_testing_data[j].append(x_norm(testing_data[j][i], minValue, maxValue))

    for i in range(len(training_data)):
        new_data[i].append(training_data[i][-1])

    for i in range(len(testing_data)):
        new_testing_data[i].append(testing_data[i][-1])

    return (new_data, new_testing_data)


if __name__ == "__main__":

    normalized_data, normalized_testing_data = minMaxNrom(training_data, testing_data)

    for row in normalized_testing_data:
        print(row)

    n_inputs = len(training_data[0]) - 1
    n_outputs = len(set([row[-1] for row in training_data]))

    network = initialize_network(n_inputs, 3, n_outputs)
    normalized_network = initialize_network(n_inputs, 3, n_outputs)

    train_network(network, training_data, 0.3, 50, n_outputs, False)
    train_network(normalized_network, normalized_data, 0.3, 50, n_outputs, False)

    prva_mreza = vtora_mreza = 0
    for i in range(len(testing_data)):
        if predict(network, testing_data[i]) == testing_data[i][-1]:
            prva_mreza += 1
        if predict(normalized_network, normalized_testing_data[i]) == normalized_testing_data[i][-1]:
            vtora_mreza += 1

    print("Prva mrezha:")
    print(prva_mreza)
    print("Vtora mrezha:")
    print(vtora_mreza)