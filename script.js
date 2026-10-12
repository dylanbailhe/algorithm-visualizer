
const canvas = document.getElementById("gridCanvas");
const ctx = canvas.getContext("2d");

let cols = 60;
let rows = 60;
let cellSize = 10;
let simulationSpeed = 10;
let currentAlgorithm = "life";

let boids = [];

const boidCount = 300;

let boidMaxSpeed = 2.5;
let boidMaxForce = 0.05;

let boidPerception = 50;

let separationWeight = 1.5;
let alignmentWeight = 1.0;
let cohesionWeight = 1.0;

let boidsMouseMode = "off";

let boidsMouseX = 0;
let boidsMouseY = 0;
let boidsMouseActive = false;

const boidsMouseRadius = 150;
const boidsMouseStrength = 3.0;

let wfcGrid = [];
let wfcTileSet = "circuit";
let wfcComplete = false;
let wfcFailed = false;
let wfcSteps = 0;

// Edge order: top, right, bottom, left
const wfcTiles = [
  { name: "empty", edges: [0, 0, 0, 0] },
  { name: "horizontal", edges: [0, 1, 0, 1] },
  { name: "vertical", edges: [1, 0, 1, 0] },
  { name: "cornerTR", edges: [1, 1, 0, 0] },
  { name: "cornerRB", edges: [0, 1, 1, 0] },
  { name: "cornerBL", edges: [0, 0, 1, 1] },
  { name: "cornerLT", edges: [1, 0, 0, 1] },
  { name: "teeTRB", edges: [1, 1, 1, 0] },
  { name: "teeRBL", edges: [0, 1, 1, 1] },
  { name: "teeBLT", edges: [1, 0, 1, 1] },
  { name: "teeLTR", edges: [1, 1, 0, 1] },
  { name: "cross", edges: [1, 1, 1, 1] }
];

const wfcTileWeights = {

  // Circuit Network: all tiles equally likely
  circuit: [
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1
  ],

  // Maze Paths: favor straight lines and corners
  maze: [
    0.5, 3, 3, 4, 4, 4,
    4, 0.15, 0.15, 0.15, 0.15, 0.05
  ],

  // Sparse Circuits: favor empty tiles
  sparse: [
    12, 1, 1, 1, 1, 1,
    1, 0.2, 0.2, 0.2, 0.2, 0.05
  ]

};

let antGrid = null;
let antRule = "RL";

let antX = 0;
let antY = 0;
let antDirection = 0;

let antSteps = 0;

// Directions: up, right, down, left
const antDX = [0, 1, 0, -1];
const antDY = [-1, 0, 1, 0];

let dlaGrid = null;
let dlaGrowthOrder = null;
let dlaParticle = null;

let dlaCount = 0;
let dlaComplete = false;

let dlaRadius = 0;
let dlaCenterX = 0;
let dlaCenterY = 0;

let noiseGrid = null;
let noiseDisplayMode = "texture";

let particles = [];

const particleCount = 2000;
const particleSpeed = 1.5;

let particleCanvas = null;
let particleCtx = null;

let noiseScale = 0.08;
let noiseOffsetX = 0;
let noiseOffsetY = 0;

let noiseSeed = 0;

let maze = [];
let mazeStack = [];
let mazeCurrent = null;
let mazeVisited = 0;
let mazeComplete = false;
let mazeComplexity = 0;
let mazeExtraWallsRemoved = false;

let bfsQueue = [];
let bfsVisited = [];
let bfsParents = [];
let bfsPath = [];

let bfsActive = false;
let bfsComplete = false;

let bfsStart = null;
let bfsEnd = null;
let bfsCurrent = null;

let dfsStack = [];
let dfsVisited = [];
let dfsParents = [];
let dfsPath = [];

let dfsActive = false;
let dfsComplete = false;
let dfsCurrent = null;

let astarOpen = [];
let astarVisited = [];
let astarClosed = [];
let astarParents = [];
let astarGScore = [];
let astarPath = [];

let astarActive = false;
let astarComplete = false;
let astarCurrent = null;

let cellsExplored = 0;
let pathLength = 0;
let searchTime = 0;

function resetPathStats() {
  cellsExplored = 0;
  pathLength = 0;
  searchTime = 0;
  updatePathStats();
}

function updatePathStats() {
  document.getElementById("cellsExplored").textContent =
    cellsExplored;

  document.getElementById("pathLength").textContent =
    pathLength > 0 ? pathLength : "—";

  document.getElementById("searchTime").textContent =
    searchTime.toFixed(2) + " ms";
}

function initializeMaze() {
  maze = [];

  for (let y = 0; y < rows; y++) {
    const row = [];

    for (let x = 0; x < cols; x++) {
      row.push({
        x: x,
        y: y,
        visited: false,
        walls: [true, true, true, true]
        // top, right, bottom, left
      });
    }

    maze.push(row);
  }

  mazeStack = [];
  mazeCurrent = maze[0][0];
  mazeCurrent.visited = true;

  mazeVisited = 1;
  mazeComplete = false;
  generation = 0;

  mazeExtraWallsRemoved = false;

  
bfsQueue = [];
bfsVisited = [];
bfsParents = [];
bfsPath = [];

bfsActive = false;
bfsComplete = false;

bfsStart = null;
bfsEnd = null;
bfsCurrent = null;

dfsStack = [];
dfsVisited = [];
dfsParents = [];
dfsPath = [];

dfsActive = false;
dfsComplete = false;
dfsCurrent = null;

astarOpen = [];
astarVisited = [];
astarClosed = [];
astarParents = [];
astarGScore = [];
astarPath = [];

astarActive = false;
astarComplete = false;
astarCurrent = null;

resetPathStats();
}

function initializeBFS() {

  if (!mazeComplete) return;

  bfsStart = maze[0][0];
  bfsEnd = maze[rows - 1][cols - 1];

  bfsQueue = [bfsStart];

  bfsVisited = Array.from(
    { length: rows },
    () => Array(cols).fill(false)
  );

  bfsParents = Array.from(
    { length: rows },
    () => Array(cols).fill(null)
  );

  bfsPath = [];

  bfsVisited[0][0] = true;

  bfsCurrent = bfsStart;
  bfsActive = true;
  bfsComplete = false;
}

function initializeDFS() {

  if (!mazeComplete) return;

  dfsStack = [maze[0][0]];

  dfsVisited = Array.from(
    { length: rows },
    () => Array(cols).fill(false)
  );

  dfsParents = Array.from(
    { length: rows },
    () => Array(cols).fill(null)
  );

  dfsPath = [];

  dfsVisited[0][0] = true;

  dfsCurrent = maze[0][0];
  dfsActive = true;
  dfsComplete = false;
}

function manhattanDistance(a, b) {
  return Math.abs(a.x - b.x) +
         Math.abs(a.y - b.y);
}

function initializeAStar() {

  if (!mazeComplete) return;

  const start = maze[0][0];

  astarOpen = [start];

  astarVisited = Array.from(
    { length: rows },
    () => Array(cols).fill(false)
  );

  astarClosed = Array.from(
    { length: rows },
    () => Array(cols).fill(false)
  );

  astarParents = Array.from(
    { length: rows },
    () => Array(cols).fill(null)
  );

  astarGScore = Array.from(
    { length: rows },
    () => Array(cols).fill(Infinity)
  );

  astarGScore[0][0] = 0;
  astarVisited[0][0] = true;

  astarPath = [];
  astarCurrent = start;

  astarActive = true;
  astarComplete = false;
}

function nextAStarStep() {

  if (!astarActive || astarComplete) return;

  const stepStart = performance.now();

  if (astarOpen.length === 0) {
    astarActive = false;
    astarComplete = true;

    searchTime += performance.now() - stepStart;
    updatePathStats();

    stopSimulation();
    return;
  }

  const end = maze[rows - 1][cols - 1];

  // Find the cell with the lowest f = g + h
  let bestIndex = 0;
  let bestScore = Infinity;

  for (let i = 0; i < astarOpen.length; i++) {
    const cell = astarOpen[i];

    const g = astarGScore[cell.y][cell.x];
    const h = manhattanDistance(cell, end);
    const f = g + h;

    if (f < bestScore) {
      bestScore = f;
      bestIndex = i;
    }
  }

  const current = astarOpen.splice(bestIndex, 1)[0];

  astarCurrent = current;
  astarClosed[current.y][current.x] = true;

  cellsExplored++;

  // Destination reached
  if (current === end) {

    astarPath = [];

    let cell = current;

    while (cell !== null) {
      astarPath.push(cell);
      cell = astarParents[cell.y][cell.x];
    }

    astarPath.reverse();

    pathLength = astarPath.length - 1;

    astarActive = false;
    astarComplete = true;

    searchTime += performance.now() - stepStart;
    updatePathStats();

    stopSimulation();
    drawGrid();
    return;
  }

  const directions = [
    [0, -1],
    [1, 0],
    [0, 1],
    [-1, 0]
  ];

  // Examine accessible neighbors
  for (let d = 0; d < 4; d++) {

    if (current.walls[d]) continue;

    const nx = current.x + directions[d][0];
    const ny = current.y + directions[d][1];

    if (
      nx < 0 || nx >= cols ||
      ny < 0 || ny >= rows
    ) continue;

    if (astarClosed[ny][nx]) continue;

    const tentativeG =
      astarGScore[current.y][current.x] + 1;

    if (tentativeG < astarGScore[ny][nx]) {

      astarGScore[ny][nx] = tentativeG;
      astarParents[ny][nx] = current;

      const neighbor = maze[ny][nx];

      if (!astarVisited[ny][nx]) {
        astarVisited[ny][nx] = true;
        astarOpen.push(neighbor);
      }
    }
  }

  searchTime += performance.now() - stepStart;
  updatePathStats();

  drawGrid();
}


function nextDFSStep() {

  if (!dfsActive || dfsComplete) return;

  // Start measuring algorithm execution time
  const stepStart = performance.now();

  // Check whether the stack is empty
  if (dfsStack.length === 0) {

    dfsActive = false;
    dfsComplete = true;

    searchTime += performance.now() - stepStart;
    updatePathStats();

    stopSimulation();
    return;
  }

  // Take the most recently discovered cell
  const current = dfsStack.pop();
  dfsCurrent = current;

  // Count this cell as explored
  cellsExplored++;

  const end = maze[rows - 1][cols - 1];

  // Check whether we reached the destination
  if (current === end) {

    dfsPath = [];

    let cell = current;

    // Reconstruct the solution path
    while (cell !== null) {
      dfsPath.push(cell);
      cell = dfsParents[cell.y][cell.x];
    }

    dfsPath.reverse();

    // Count edges rather than cells
    pathLength = dfsPath.length - 1;

    dfsActive = false;
    dfsComplete = true;

    // Record the final calculation time
    searchTime += performance.now() - stepStart;
    updatePathStats();

    stopSimulation();
    drawGrid();
    return;
  }

  // Directions: top, right, bottom, left
  const directions = [
    [0, -1],
    [1, 0],
    [0, 1],
    [-1, 0]
  ];

  // Explore neighboring cells
  for (let d = 0; d < 4; d++) {

    if (!current.walls[d]) {

      const nx = current.x + directions[d][0];
      const ny = current.y + directions[d][1];

      if (
        nx >= 0 && nx < cols &&
        ny >= 0 && ny < rows &&
        !dfsVisited[ny][nx]
      ) {

        dfsVisited[ny][nx] = true;

        const neighbor = maze[ny][nx];

        dfsParents[ny][nx] = current;
        dfsStack.push(neighbor);
      }
    }
  }

  // Add this step's execution time
  searchTime += performance.now() - stepStart;

  // Update the statistics panel
  updatePathStats();

  // Redraw the maze
  drawGrid();
}


function nextBFSStep() {

  if (!bfsActive || bfsComplete) return;

  const stepStart = performance.now();

  if (bfsQueue.length === 0) {
    bfsActive = false;
    bfsComplete = true;
    stopSimulation();
    return;
  }

  const current = bfsQueue.shift();
  bfsCurrent = current;

  cellsExplored++;

  if (current === bfsEnd) {

    bfsPath = [];

    let cell = current;

    while (cell !== null) {
      bfsPath.push(cell);
      cell = bfsParents[cell.y][cell.x];
    }

    bfsPath.reverse();

    pathLength = bfsPath.length - 1;

    bfsActive = false;
    bfsComplete = true;

    searchTime += performance.now() - stepStart;
    updatePathStats();

    stopSimulation();
    drawGrid();
    return;
  }

  const directions = [
    [0, -1],
    [1, 0],
    [0, 1],
    [-1, 0]
  ];

  for (let d = 0; d < 4; d++) {

    if (!current.walls[d]) {

      const nx = current.x + directions[d][0];
      const ny = current.y + directions[d][1];

      if (
        nx >= 0 && nx < cols &&
        ny >= 0 && ny < rows &&
        !bfsVisited[ny][nx]
      ) {

        bfsVisited[ny][nx] = true;

        const neighbor = maze[ny][nx];

        bfsParents[ny][nx] = current;
        bfsQueue.push(neighbor);
      }
    }
  }
searchTime += performance.now() - stepStart;
updatePathStats();

  drawGrid();
}


function nextMazeGeneration() {
  if (mazeComplete) return;

  const { x, y } = mazeCurrent;
  const neighbors = [];

  if (y > 0 && !maze[y - 1][x].visited)
    neighbors.push({ cell: maze[y - 1][x], direction: 0 });

  if (x < cols - 1 && !maze[y][x + 1].visited)
    neighbors.push({ cell: maze[y][x + 1], direction: 1 });

  if (y < rows - 1 && !maze[y + 1][x].visited)
    neighbors.push({ cell: maze[y + 1][x], direction: 2 });

  if (x > 0 && !maze[y][x - 1].visited)
    neighbors.push({ cell: maze[y][x - 1], direction: 3 });

  if (neighbors.length > 0) {

    const choice = neighbors[
      Math.floor(Math.random() * neighbors.length)
    ];

    const next = choice.cell;
    const direction = choice.direction;

    mazeCurrent.walls[direction] = false;
    next.walls[(direction + 2) % 4] = false;

    mazeStack.push(mazeCurrent);

    mazeCurrent = next;
    mazeCurrent.visited = true;
    mazeVisited++;

  } else if (mazeStack.length > 0) {

    mazeCurrent = mazeStack.pop();

  
    } else {

    // Maze generation has finished
    mazeComplete = true;

    // Create additional routes
    addMazeConnections();

    stopSimulation();
    }


  generation++;
  drawGrid();
}


function addMazeConnections() {

  if (mazeExtraWallsRemoved) return;

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const cell = maze[y][x];

      // Consider removing the right wall
      if (x < cols - 1 && cell.walls[1]) {

        if (Math.random() < mazeComplexity / 100) {
          cell.walls[1] = false;
          maze[y][x + 1].walls[3] = false;
        }
      }

      // Consider removing the bottom wall
      if (y < rows - 1 && cell.walls[2]) {

        if (Math.random() < mazeComplexity / 100) {
          cell.walls[2] = false;
          maze[y + 1][x].walls[0] = false;
        }
      }
    }
  }

  mazeExtraWallsRemoved = true;
}


function drawMaze() {
  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;

  ctx.lineWidth = Math.max(1, sizeX * 0.12);
  ctx.strokeStyle = "#38bdf8";

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const cell = maze[y][x];

      const px = x * sizeX;
      const py = y * sizeY;

      if (cell.visited) {
        ctx.fillStyle = "#14283c";
        ctx.fillRect(px, py, sizeX, sizeY);
      }

      ctx.beginPath();

      if (cell.walls[0]) {
        ctx.moveTo(px, py);
        ctx.lineTo(px + sizeX, py);
      }

      if (cell.walls[1]) {
        ctx.moveTo(px + sizeX, py);
        ctx.lineTo(px + sizeX, py + sizeY);
      }

      if (cell.walls[2]) {
        ctx.moveTo(px, py + sizeY);
        ctx.lineTo(px + sizeX, py + sizeY);
      }

      if (cell.walls[3]) {
        ctx.moveTo(px, py);
        ctx.lineTo(px, py + sizeY);
      }

      ctx.stroke();
    }
  }

// Draw BFS explored cells

const activeVisited =
  astarVisited.length > 0 ? astarVisited :
  dfsVisited.length > 0 ? dfsVisited :
  bfsVisited;


if (activeVisited.length > 0) {
  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      if (activeVisited[y][x]) {
        ctx.fillStyle = "#2563eb";

        ctx.fillRect(
          x * sizeX + sizeX * 0.2,
          y * sizeY + sizeY * 0.2,
          sizeX * 0.6,
          sizeY * 0.6
        );
      }
    }
  }
}

// Draw shortest path

const activePath =
  astarPath.length > 0 ? astarPath :
  dfsPath.length > 0 ? dfsPath :
  bfsPath;


for (const cell of activePath) {
  ctx.fillStyle = "#facc15";

  ctx.fillRect(
    cell.x * sizeX + sizeX * 0.15,
    cell.y * sizeY + sizeY * 0.15,
    sizeX * 0.7,
    sizeY * 0.7
  );
}

// Draw start and end
if (mazeComplete) {

  ctx.fillStyle = "#22c55e";
  ctx.fillRect(2, 2, sizeX - 4, sizeY - 4);

  ctx.fillStyle = "#ef4444";
  ctx.fillRect(
    (cols - 1) * sizeX + 2,
    (rows - 1) * sizeY + 2,
    sizeX - 4,
    sizeY - 4
  );
}

  if (mazeCurrent && !mazeComplete) {
    ctx.fillStyle = "#facc15";

    ctx.fillRect(
      mazeCurrent.x * sizeX + 2,
      mazeCurrent.y * sizeY + 2,
      Math.max(1, sizeX - 4),
      Math.max(1, sizeY - 4)
    );
  }

  document.getElementById("generation").textContent =
    "Generation: " + generation;
}


let currentPalette = "ocean";
let numStates = 16;

let chemicalA = null;
let chemicalB = null;

const diffusionA = 1.0;
const diffusionB = 0.5;
const reactionTimeStep = 0.2;

let feedRate = 0.055;
let killRate = 0.062;


// Smooth interpolation
function smoothstep(t) {
  return t * t * (3 - 2 * t);
}

// Linear interpolation
function lerp(a, b, t) {
  return a + (b - a) * t;
}

// Deterministic pseudorandom lattice value
function noiseRandom(x, y) {
  let n = Math.sin(
    x * 127.1 +
    y * 311.7 +
    noiseSeed * 74.7
  ) * 43758.5453;

  return n - Math.floor(n);
}

// Smooth 2D value noise
function valueNoise(x, y) {
  const x0 = Math.floor(x);
  const y0 = Math.floor(y);

  const x1 = x0 + 1;
  const y1 = y0 + 1;

  const tx = smoothstep(x - x0);
  const ty = smoothstep(y - y0);

  const a = noiseRandom(x0, y0);
  const b = noiseRandom(x1, y0);
  const c = noiseRandom(x0, y1);
  const d = noiseRandom(x1, y1);

  const top = lerp(a, b, tx);
  const bottom = lerp(c, d, tx);

  return lerp(top, bottom, ty);
}


function initializeParticles() {

  particles = [];

  // Create an offscreen canvas for trails
  particleCanvas = document.createElement("canvas");

  particleCanvas.width = canvas.width;
  particleCanvas.height = canvas.height;

  particleCtx = particleCanvas.getContext("2d");

  particleCtx.fillStyle = "#080c14";
  particleCtx.fillRect(
    0, 0,
    particleCanvas.width,
    particleCanvas.height
  );

  // Distribute particles randomly
  for (let i = 0; i < particleCount; i++) {

    particles.push({
      x: Math.random() * canvas.width,
      y: Math.random() * canvas.height
    });

  }
}


function sampleSmoothNoise(px, py) {

  // Convert canvas coordinates to grid coordinates
  const gx = px / canvas.width * cols;
  const gy = py / canvas.height * rows;

  const x0 = Math.floor(gx);
  const y0 = Math.floor(gy);

  const x1 = (x0 + 1) % cols;
  const y1 = (y0 + 1) % rows;

  const ix0 = ((x0 % cols) + cols) % cols;
  const iy0 = ((y0 % rows) + rows) % rows;

  // Fractional position within the grid cell
  const tx = gx - x0;
  const ty = gy - y0;

  // Read four neighboring noise values
  const a = noiseGrid[iy0 * cols + ix0];
  const b = noiseGrid[iy0 * cols + x1];
  const c = noiseGrid[y1 * cols + ix0];
  const d = noiseGrid[y1 * cols + x1];

  // Interpolate horizontally
  const top = a + (b - a) * tx;
  const bottom = c + (d - c) * tx;

  // Interpolate vertically
  return top + (bottom - top) * ty;
}


function updateParticles() {

  if (!particleCtx || !particleCanvas) {
    initializeParticles();
  }

  // Fade old trails
  particleCtx.fillStyle = "rgba(8, 12, 20, 0.04)";

  particleCtx.fillRect(
    0, 0,
    particleCanvas.width,
    particleCanvas.height
  );

  particleCtx.strokeStyle = "rgba(0, 255, 80, 0.75)";

  particleCtx.lineWidth = 0.7;

  for (const particle of particles) {

    const oldX = particle.x;
    const oldY = particle.y;

    // Smoothly sample the noise field
    const value = sampleSmoothNoise(
    particle.x,
    particle.y
    );

    // Convert noise into a direction
    const angle = value * Math.PI * 2;

    particle.x += Math.cos(angle) * particleSpeed;
    particle.y += Math.sin(angle) * particleSpeed;

    // Wrap particles around canvas edges
    if (
      particle.x < 0 ||
      particle.x >= canvas.width ||
      particle.y < 0 ||
      particle.y >= canvas.height
    ) {
      particle.x =
        (particle.x + canvas.width) % canvas.width;

      particle.y =
        (particle.y + canvas.height) % canvas.height;

      // Don't draw a long line across the canvas
      continue;
    }

    // Draw particle trail
    particleCtx.beginPath();
    particleCtx.moveTo(oldX, oldY);
    particleCtx.lineTo(particle.x, particle.y);
    particleCtx.stroke();
  }
}

function chooseWFCTile(options) {

  const weights = wfcTileWeights[wfcTileSet];

  let totalWeight = 0;

  for (const option of options) {
    totalWeight += weights[option];
  }

  let random = Math.random() * totalWeight;

  for (const option of options) {

    random -= weights[option];

    if (random < 0) {
      return option;
    }
  }

  return options[options.length - 1];
}

function initializeBoids() {

  boids = [];

  for (let i = 0; i < boidCount; i++) {

    const angle = Math.random() * Math.PI * 2;

    boids.push({
      x: Math.random() * canvas.width,
      y: Math.random() * canvas.height,

      vx: Math.cos(angle) * boidMaxSpeed,
      vy: Math.sin(angle) * boidMaxSpeed
    });

  }

  generation = 0;
}


function steerBoid(
  desiredX,
  desiredY,
  currentVX,
  currentVY
) {

  const magnitude = Math.hypot(desiredX, desiredY);

  if (magnitude === 0) {
    return { x: 0, y: 0 };
  }

  // Desired velocity
  desiredX = desiredX / magnitude * boidMaxSpeed;
  desiredY = desiredY / magnitude * boidMaxSpeed;

  // Steering force
  let steerX = desiredX - currentVX;
  let steerY = desiredY - currentVY;

  const force = Math.hypot(steerX, steerY);

  if (force > boidMaxForce) {
    steerX = steerX / force * boidMaxForce;
    steerY = steerY / force * boidMaxForce;
  }

  return { x: steerX, y: steerY };
}


function updateBoids() {

  const nextVelocities = [];

  for (const boid of boids) {

    let sepX = 0;
    let sepY = 0;

    let alignX = 0;
    let alignY = 0;

    let cohesionX = 0;
    let cohesionY = 0;

    let neighborCount = 0;
    let separationCount = 0;

    for (const other of boids) {

      if (boid === other) continue;

      const dx = other.x - boid.x;
      const dy = other.y - boid.y;

      const distance = Math.hypot(dx, dy);

      if (distance < boidPerception && distance > 0) {

        // Alignment
        alignX += other.vx;
        alignY += other.vy;

        // Cohesion: relative positions
        cohesionX += dx;
        cohesionY += dy;

        neighborCount++;

        // Separation
        if (distance < boidPerception * 0.5) {

          sepX -= dx / (distance * distance);
          sepY -= dy / (distance * distance);

          separationCount++;
        }
      }
    }

    let forceX = 0;
    let forceY = 0;

    if (neighborCount > 0) {

      // Alignment
      const align = steerBoid(
        alignX / neighborCount,
        alignY / neighborCount,
        boid.vx,
        boid.vy
      );

      // Cohesion
      const cohesion = steerBoid(
        cohesionX / neighborCount,
        cohesionY / neighborCount,
        boid.vx,
        boid.vy
      );

      forceX += align.x * alignmentWeight;
      forceY += align.y * alignmentWeight;

      forceX += cohesion.x * cohesionWeight;
      forceY += cohesion.y * cohesionWeight;
    }

    if (separationCount > 0) {

      const separation = steerBoid(
        sepX / separationCount,
        sepY / separationCount,
        boid.vx,
        boid.vy
      );

      forceX += separation.x * separationWeight;
      forceY += separation.y * separationWeight;
    }


    // Mouse attraction or repulsion
    if (
    boidsMouseActive &&
    boidsMouseMode !== "off"
    ) {

    const dx = boidsMouseX - boid.x;
    const dy = boidsMouseY - boid.y;

    const distance = Math.hypot(dx, dy);

    if (
        distance > 0 &&
        distance < boidsMouseRadius
    ) {

        // Stronger effect near the cursor
        const influence =
        1 - distance / boidsMouseRadius;

        const direction =
        boidsMouseMode === "attract" ? 1 : -1;

        const mouseForce = steerBoid(
        dx * direction,
        dy * direction,
        boid.vx,
        boid.vy
        );

        forceX += mouseForce.x *
        boidsMouseStrength * influence;

        forceY += mouseForce.y *
        boidsMouseStrength * influence;
    }
    }

    let vx = boid.vx + forceX;
    let vy = boid.vy + forceY;

    // Limit velocity
    const speed = Math.hypot(vx, vy);

    if (speed > boidMaxSpeed) {
      vx = vx / speed * boidMaxSpeed;
      vy = vy / speed * boidMaxSpeed;
    }

    nextVelocities.push({ vx, vy });
  }

  // Apply velocities after all forces are calculated
  for (let i = 0; i < boids.length; i++) {

    const boid = boids[i];

    boid.vx = nextVelocities[i].vx;
    boid.vy = nextVelocities[i].vy;

    boid.x += boid.vx;
    boid.y += boid.vy;

    // Wrap around screen boundaries
    boid.x = (boid.x + canvas.width) % canvas.width;
    boid.y = (boid.y + canvas.height) % canvas.height;
  }

  generation++;
}


function drawBoids() {

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.fillStyle = "#00ff50";

  for (const boid of boids) {

    const angle = Math.atan2(boid.vy, boid.vx);

    ctx.save();

    ctx.translate(boid.x, boid.y);
    ctx.rotate(angle);

    // Draw a small triangle pointing forward
    ctx.beginPath();

    ctx.moveTo(8, 0);
    ctx.lineTo(-5, -4);
    ctx.lineTo(-5, 4);

    ctx.closePath();
    ctx.fill();

    ctx.restore();
  }

  document.getElementById("generation").textContent =
    "Boids: " + boids.length +
    " | Simulation Steps: " + generation;
}


function initializeWFC() {

  wfcGrid = [];

  for (let y = 0; y < rows; y++) {
    const row = [];

    for (let x = 0; x < cols; x++) {

      // Every tile is initially possible
      const options = wfcTiles.map((_, i) => i);

      // Prevent connections leaving the grid
      const validOptions = options.filter(i => {
        const e = wfcTiles[i].edges;

        if (y === 0 && e[0] === 1) return false;
        if (x === cols - 1 && e[1] === 1) return false;
        if (y === rows - 1 && e[2] === 1) return false;
        if (x === 0 && e[3] === 1) return false;

        return true;
      });

      row.push({
        options: validOptions,
        collapsed: false
      });
    }

    wfcGrid.push(row);
  }

  wfcComplete = false;
  wfcFailed = false;
  wfcSteps = 0;
  generation = 0;

// Start with a random tile in the center
const centerX = Math.floor(cols / 2);
const centerY = Math.floor(rows / 2);

const centerCell = wfcGrid[centerY][centerX];

const selected = chooseWFCTile(centerCell.options);

centerCell.options = [selected];
centerCell.collapsed = true;

// Propagate the center tile's constraints
if (!propagateWFC(centerX, centerY)) {
  wfcFailed = true;
}

}


function propagateWFC(startX, startY) {

  const queue = [[startX, startY]];
  let head = 0;

  const directions = [
    [0, -1],
    [1, 0],
    [0, 1],
    [-1, 0]
  ];

  while (head < queue.length) {

    const [x, y] = queue[head++];
    const source = wfcGrid[y][x];

    for (let d = 0; d < 4; d++) {

      const nx = x + directions[d][0];
      const ny = y + directions[d][1];

      if (
        nx < 0 || nx >= cols ||
        ny < 0 || ny >= rows
      ) continue;

      const neighbor = wfcGrid[ny][nx];
      const opposite = (d + 2) % 4;

      const allowed = neighbor.options.filter(n => {

        return source.options.some(s =>
          wfcTiles[s].edges[d] ===
          wfcTiles[n].edges[opposite]
        );
      });

      if (allowed.length === 0) {
        return false;
      }

      if (allowed.length < neighbor.options.length) {
        neighbor.options = allowed;
        queue.push([nx, ny]);
      }
    }
  }

  return true;
}

function nextWFCStep() {

  if (wfcComplete || wfcFailed) return;

  let candidates = [];
  let lowestEntropy = Infinity;

  const directions = [
    [0, -1],
    [1, 0],
    [0, 1],
    [-1, 0]
  ];

  // Find undecided cells next to resolved cells
  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const cell = wfcGrid[y][x];

      if (cell.options.length <= 1) continue;

      let hasResolvedNeighbor = false;

      for (const [dx, dy] of directions) {

        const nx = x + dx;
        const ny = y + dy;

        if (
          nx < 0 || nx >= cols ||
          ny < 0 || ny >= rows
        ) continue;

        if (wfcGrid[ny][nx].options.length === 1) {
          hasResolvedNeighbor = true;
          break;
        }
      }

      if (!hasResolvedNeighbor) continue;

      // Prefer lower entropy within the frontier
      const entropy = cell.options.length;

      if (entropy < lowestEntropy) {
        lowestEntropy = entropy;
        candidates = [[x, y]];

      } else if (entropy === lowestEntropy) {
        candidates.push([x, y]);
      }
    }
  }

  // Fallback if no frontier cells remain
  if (candidates.length === 0) {

    for (let y = 0; y < rows; y++) {
      for (let x = 0; x < cols; x++) {

        if (wfcGrid[y][x].options.length > 1) {
          candidates.push([x, y]);
        }
      }
    }
  }

  // All cells have been resolved
  if (candidates.length === 0) {
    wfcComplete = true;
    stopSimulation();
    drawGrid();
    return;
  }

  // Randomly select a frontier cell
  const [x, y] = candidates[
    Math.floor(Math.random() * candidates.length)
  ];

  const cell = wfcGrid[y][x];

  // Select one of its possible tiles
  const selected = chooseWFCTile(cell.options);

  cell.options = [selected];
  cell.collapsed = true;

  // Propagate constraints
  if (!propagateWFC(x, y)) {
    wfcFailed = true;
    stopSimulation();
    drawGrid();
    return;
  }

  wfcSteps++;
  generation++;
}

function drawWFC() {

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;

  ctx.strokeStyle = "#00ff50";
  ctx.lineWidth = Math.max(
    1,
    Math.min(sizeX, sizeY) * 0.18
  );
  ctx.lineCap = "round";

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const cell = wfcGrid[y][x];

      // Only draw determined cells
      if (cell.options.length !== 1) continue;

      const tile = wfcTiles[cell.options[0]];

      const cx = (x + 0.5) * sizeX;
      const cy = (y + 0.5) * sizeY;

      const halfX = sizeX / 2;
      const halfY = sizeY / 2;

      ctx.beginPath();

      for (let d = 0; d < 4; d++) {

        if (!tile.edges[d]) continue;

        let ex = cx;
        let ey = cy;

        if (d === 0) ey -= halfY;
        if (d === 1) ex += halfX;
        if (d === 2) ey += halfY;
        if (d === 3) ex -= halfX;

        ctx.moveTo(cx, cy);
        ctx.lineTo(ex, ey);
      }

      ctx.stroke();
    }
  }

  document.getElementById("generation").textContent =
    wfcFailed
      ? "WFC: Contradiction — click Randomize"
      : wfcComplete
        ? "WFC: Complete"
        : "WFC Collapses: " + wfcSteps;
}


function initializeAnt() {

  antGrid = new Uint8Array(cols * rows);

  // Start in the center of the screen
  antX = Math.floor(cols / 2);
  antY = Math.floor(rows / 2);

  antDirection = 0;
  antSteps = 0;

  generation = 0;
}


function nextAntStep() {

  const index = antY * cols + antX;

  // Read the current cell's color state
  const state = antGrid[index];

  // Get the turning rule for this state
  const turn = antRule[state];

  if (turn === "R") {

    antDirection = (antDirection + 1) % 4;

  } else if (turn === "L") {

    antDirection = (antDirection + 3) % 4;

  }

  // Advance to the next color state
  antGrid[index] = (state + 1) % antRule.length;

  // Move forward
  antX += antDX[antDirection];
  antY += antDY[antDirection];

  // Wrap around the grid
  antX = (antX + cols) % cols;
  antY = (antY + rows) % rows;

  antSteps++;
  generation++;
}



function drawAnt() {

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;


// Draw cells according to their color state
for (let y = 0; y < rows; y++) {
  for (let x = 0; x < cols; x++) {

    const state = antGrid[y * cols + x];

    if (state > 0) {

      const hue = 140 + 
        (state / antRule.length) * 180;

      ctx.fillStyle = `hsl(${hue}, 95%, 55%)`;

      ctx.fillRect(
        x * sizeX,
        y * sizeY,
        sizeX,
        sizeY
      );

    }
  }
}


  // Draw the ant in yellow
  ctx.fillStyle = "#facc15";

  ctx.fillRect(
    antX * sizeX,
    antY * sizeY,
    sizeX,
    sizeY
  );

  document.getElementById("generation").textContent =
    "Ant Steps: " + antSteps;
}


function initializeDLA() {

  dlaGrid = new Uint8Array(cols * rows);
  dlaGrowthOrder = new Uint32Array(cols * rows);

  dlaCenterX = Math.floor(cols / 2);
  dlaCenterY = Math.floor(rows / 2);

  // Place the initial seed
  dlaGrid[dlaCenterY * cols + dlaCenterX] = 1;
  dlaGrowthOrder[dlaCenterY * cols + dlaCenterX] = 1;

  dlaCount = 1;
  dlaRadius = 0;
  dlaComplete = false;
  dlaParticle = null;

  generation = 0;

  spawnDLAParticle();
}


function spawnDLAParticle() {

  if (dlaComplete) return;

  // Launch particles just outside the cluster
  const launchRadius = Math.min(
    Math.min(cols, rows) * 0.45,
    Math.max(5, dlaRadius + 4)
  );

  const angle = Math.random() * Math.PI * 2;

  const x = Math.round(
    dlaCenterX + Math.cos(angle) * launchRadius
  );

  const y = Math.round(
    dlaCenterY + Math.sin(angle) * launchRadius
  );

  dlaParticle = {
    x: Math.max(1, Math.min(cols - 2, x)),
    y: Math.max(1, Math.min(rows - 2, y))
  };
}


function nextDLAStep() {

  if (dlaComplete) return;

  if (!dlaParticle) {
    spawnDLAParticle();
  }

  const p = dlaParticle;

  // Random movement
  const direction = Math.floor(Math.random() * 4);

  if (direction === 0) p.x++;
  if (direction === 1) p.x--;
  if (direction === 2) p.y++;
  if (direction === 3) p.y--;

  // Keep particle inside the grid
  p.x = Math.max(1, Math.min(cols - 2, p.x));
  p.y = Math.max(1, Math.min(rows - 2, p.y));
  
// Restart particles that wander too far away
const killRadius = Math.min(
  Math.min(cols, rows) * 0.49,
  Math.max(12, dlaRadius + 12)
);

const distanceFromCenter = Math.hypot(
  p.x - dlaCenterX,
  p.y - dlaCenterY
);

if (distanceFromCenter > killRadius) {
  spawnDLAParticle();
  generation++;
  return;
}

  const neighbors = [
    [1, 0],
    [-1, 0],
    [0, 1],
    [0, -1]
  ];

  // Check whether the particle touches the cluster
  for (const [dx, dy] of neighbors) {

    const nx = p.x + dx;
    const ny = p.y + dy;

    if (dlaGrid[ny * cols + nx] === 1) {

      // Attach particle permanently
      const index = p.y * cols + p.x;

      if (dlaGrid[index] === 0) {

        dlaGrid[index] = 1;
        dlaCount++;
        dlaGrowthOrder[index] = dlaCount;

        const distance = Math.hypot(
          p.x - dlaCenterX,
          p.y - dlaCenterY
        );

        dlaRadius = Math.max(dlaRadius, distance);
      }

      spawnDLAParticle();
      break;
    }
  }

  generation++;

  // Stop when the cluster approaches the boundary
  if (dlaRadius >= Math.min(cols, rows) * 0.42) {
    dlaComplete = true;
    stopSimulation();
  }
}

function getDLAColor(order) {

  // Normalize growth order between 0 and 1
  const t = dlaCount > 1
    ? (order - 1) / (dlaCount - 1)
    : 0;

  // Old particles: deep blue
  // New particles: bright cyan
  const hue = 230 - t * 40;

  const saturation = 90;
  const lightness = 25 + t * 35;

  return `hsl(${hue}, ${saturation}%, ${lightness}%)`;
}


function drawDLA() {

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;

  // Draw the permanent cluster
  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      if (dlaGrid[y * cols + x] === 1) {

    const index = y * cols + x;
    const order = dlaGrowthOrder[index];

    ctx.fillStyle = getDLAColor(order);

        ctx.fillRect(
          x * sizeX,
          y * sizeY,
          sizeX,
          sizeY
        );
      }
    }
  }

  // Draw the moving particle in yellow
  if (dlaParticle && !dlaComplete) {

    ctx.fillStyle = "#facc15";

    ctx.fillRect(
      dlaParticle.x * sizeX,
      dlaParticle.y * sizeY,
      sizeX,
      sizeY
    );
  }

  document.getElementById("generation").textContent =
    "Random Walk Steps: " + generation +
    " | Cluster Particles: " + dlaCount;
}


function initializeNoise() {

  noiseSeed = Math.random() * 10000;

  noiseOffsetX = Math.random() * 1000;
  noiseOffsetY = Math.random() * 1000;

  noiseGrid = new Float32Array(cols * rows);

  updateNoiseGrid();

  generation = 0;

  if (noiseDisplayMode === "particles") {
  initializeParticles();
}
}

function updateNoiseGrid() {

  if (!noiseGrid || noiseGrid.length !== cols * rows) {
    noiseGrid = new Float32Array(cols * rows);
  }

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const nx = x * noiseScale + noiseOffsetX;
      const ny = y * noiseScale + noiseOffsetY;

      noiseGrid[y * cols + x] = valueNoise(nx, ny);
    }
  }
}


function initializeReaction() {
  const total = cols * rows;

  chemicalA = new Float32Array(total);
  chemicalB = new Float32Array(total);

  chemicalA.fill(1.0);

  // Add several small patches of chemical B.
  for (let patch = 0; patch < 12; patch++) {
    const centerX = Math.floor(Math.random() * cols);
    const centerY = Math.floor(Math.random() * rows);

    const radius = Math.max(2, Math.floor(cols / 35));

    for (let dy = -radius; dy <= radius; dy++) {
      for (let dx = -radius; dx <= radius; dx++) {
        const x = (centerX + dx + cols) % cols;
        const y = (centerY + dy + rows) % rows;

        const index = y * cols + x;

        chemicalA[index] = 0;
        chemicalB[index] = 1;
      }
    }
  }

  generation = 0;
}

function injectChemicalB(centerX, centerY) {

  if (!chemicalA || !chemicalB) return;

  const radius = Math.max(2, Math.floor(cols / 60));

  for (let dy = -radius; dy <= radius; dy++) {
    for (let dx = -radius; dx <= radius; dx++) {

      // Create a circular brush
      if (dx * dx + dy * dy > radius * radius) {
        continue;
      }

      const x = (centerX + dx + cols) % cols;
      const y = (centerY + dy + rows) % rows;

      const index = y * cols + x;

      chemicalA[index] = 0.0;
      chemicalB[index] = 1.0;
    }
  }

  drawGrid();
}


function nextReactionGeneration() {
  if (!chemicalA || !chemicalB) {
    initializeReaction();
  }

  const nextA = new Float32Array(cols * rows);
  const nextB = new Float32Array(cols * rows);

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const i = y * cols + x;

      const left = y * cols + (x - 1 + cols) % cols;
      const right = y * cols + (x + 1) % cols;

      const up = ((y - 1 + rows) % rows) * cols + x;
      const down = ((y + 1) % rows) * cols + x;

      const a = chemicalA[i];
      const b = chemicalB[i];

      const laplaceA =
        chemicalA[left] +
        chemicalA[right] +
        chemicalA[up] +
        chemicalA[down] -
        4 * a;

      const laplaceB =
        chemicalB[left] +
        chemicalB[right] +
        chemicalB[up] +
        chemicalB[down] -
        4 * b;

      const reaction = a * b * b;

      
        nextA[i] = Math.max(0, Math.min(1,
        a + (
            diffusionA * laplaceA
            - reaction
            + feedRate * (1 - a)
        ) * reactionTimeStep
        ));

        nextB[i] = Math.max(0, Math.min(1,
        b + (
            diffusionB * laplaceB
            + reaction
            - (killRate + feedRate) * b
        ) * reactionTimeStep
        ));

    }
  }

  chemicalA = nextA;
  chemicalB = nextB;

  generation++;
}


// The shorter viewport dimension determines the grid resolution.
// The longer dimension gains extra rows or columns, keeping cells square.
function resizeCanvasGeometry() {
  const resolution = Number(document.getElementById("gridSizeSelect").value);
  const width = Math.max(1, window.innerWidth);
  const height = Math.max(1, window.innerHeight);
  cellSize = Math.min(width, height) / resolution;
  cols = Math.ceil(width / cellSize);
  rows = Math.ceil(height / cellSize);
  canvas.width = width;
  canvas.height = height;
}
resizeCanvasGeometry();

let grid = createGrid();
let generation = 0;
let running = false;

function createGrid() {
  return Array.from(
    { length: rows },
    () => Array(cols).fill(0)
  );
}

function getReactionColor(b) {

  // Normalize chemical B concentration
  const intensity = Math.max(0, Math.min(1, b * 2.5));

  if (currentPalette === "ocean") {
    const r = Math.floor(intensity * 15);
    const g = Math.floor(intensity * 200);
    const blue = Math.floor(intensity * 255);

    return `rgb(${r}, ${g}, ${blue})`;
  }

  if (currentPalette === "rainbow") {
    const hue = (1 - intensity) * 270;

    return `hsl(${hue}, 90%, ${10 + intensity * 55}%)`;
  }

  if (currentPalette === "grayscale") {
    const value = Math.floor(intensity * 255);

    return `rgb(${value}, ${value}, ${value})`;
  }

  if (currentPalette === "heat") {
    const hue = 270 - intensity * 225;

    return `hsl(${hue}, 100%, ${5 + intensity * 55}%)`;
  }

  return "#000000";
}


function drawVectorField() {

  // Dark background
  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;

  // Draw fewer arrows than grid cells
  const spacing = Math.max(1, Math.floor(cols / 20));

  ctx.strokeStyle = "#38bdf8";
  ctx.fillStyle = "#38bdf8";
  ctx.lineWidth = 1.5;

  for (let y = 0; y < rows; y += spacing) {
    for (let x = 0; x < cols; x += spacing) {

      const value = noiseGrid[y * cols + x];

      // Convert noise into an angle
      const angle = value * Math.PI * 2;

      const dx = Math.cos(angle);
      const dy = Math.sin(angle);

      const centerX = (x + 0.5) * sizeX;
      const centerY = (y + 0.5) * sizeY;

      const length = Math.min(
        sizeX * spacing,
        sizeY * spacing
      ) * 0.35;

      const endX = centerX + dx * length;
      const endY = centerY + dy * length;

      // Draw arrow shaft
      ctx.beginPath();
      ctx.moveTo(
        centerX - dx * length * 0.5,
        centerY - dy * length * 0.5
      );
      ctx.lineTo(endX, endY);
      ctx.stroke();

      // Draw arrowhead
      const headSize = Math.max(2, length * 0.3);

      const leftAngle = angle + Math.PI * 0.75;
      const rightAngle = angle - Math.PI * 0.75;

      ctx.beginPath();
      ctx.moveTo(endX, endY);

      ctx.lineTo(
        endX + Math.cos(leftAngle) * headSize,
        endY + Math.sin(leftAngle) * headSize
      );

      ctx.moveTo(endX, endY);

      ctx.lineTo(
        endX + Math.cos(rightAngle) * headSize,
        endY + Math.sin(rightAngle) * headSize
      );

      ctx.stroke();
    }
  }

  document.getElementById("generation").textContent =
    "Generation: " + generation;
}


function drawParticleFlow() {

  if (!particleCanvas) {
    initializeParticles();
  }

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.drawImage(particleCanvas, 0, 0);

  document.getElementById("generation").textContent =
    "Generation: " + generation;
}


function drawGrid() {

if (currentAlgorithm === "boids") {
  drawBoids();
  return;
}

if (currentAlgorithm === "wfc") {
  drawWFC();
  return;
}

if (currentAlgorithm === "ant") {
  drawAnt();
  return;
}

if (currentAlgorithm === "dla") {
  drawDLA();
  return;
}

if (currentAlgorithm === "maze") {
  drawMaze();
  return;
}

if (
  currentAlgorithm === "noise" &&
  noiseDisplayMode === "particles"
) {
  drawParticleFlow();
  return;
}

if (
  currentAlgorithm === "noise" &&
  noiseDisplayMode === "vectors"
) {
  drawVectorField();
  return;
}

if (currentAlgorithm === "noise") {

  ctx.fillStyle = "#080c14";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const sizeX = canvas.width / cols;
  const sizeY = canvas.height / rows;

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const value = noiseGrid
        ? noiseGrid[y * cols + x]
        : 0;

      const brightness = Math.floor(value * 255);

      ctx.fillStyle =
        `rgb(${brightness}, ${brightness}, ${brightness})`;

      ctx.fillRect(
        x * sizeX,
        y * sizeY,
        sizeX + 0.5,
        sizeY + 0.5
      );
    }
  }

  document.getElementById("generation").textContent =
    "Generation: " + generation;

  return;
}

  ctx.fillStyle = "#101827";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {
      
    if (currentAlgorithm === "life") {

    ctx.fillStyle =
        grid[y][x] === 1 ? "#38bdf8" : "#172235";

    } else if (currentAlgorithm === "cyclic") {

    const hue = (grid[y][x] / numStates) * 360;

    ctx.fillStyle = `hsl(${hue}, 85%, 50%)`;

    }

    
    else if (currentAlgorithm === "reaction") {

    const index = y * cols + x;
    const b = chemicalB ? chemicalB[index] : 0;

    ctx.fillStyle = getReactionColor(b);

    }


      ctx.fillRect(
        x * cellSize + 0.5,
        y * cellSize + 0.5,
        Math.max(0.5, cellSize - 1),
        Math.max(0.5, cellSize - 1)
      );
    }
  }

  document.getElementById("generation").textContent =
    "Generation: " + generation;
}

function randomize() {
  stopSimulation();
  
if (currentAlgorithm === "boids") {

  initializeBoids();

} else if (currentAlgorithm === "wfc") {

  initializeWFC();

} else if (currentAlgorithm === "ant") {

  initializeAnt();

} else if (currentAlgorithm === "dla") {

  initializeDLA();

} else if (currentAlgorithm === "noise") {

  initializeNoise();

} else if (currentAlgorithm === "maze") {

  initializeMaze();

} else if (currentAlgorithm === "reaction") {

  initializeReaction();

  } else {

    grid = Array.from(
      { length: rows },
      () => Array.from(
        { length: cols },
        () => {
          if (currentAlgorithm === "cyclic") {
            return Math.floor(Math.random() * numStates);
          } else {
            return Math.random() < 0.3 ? 1 : 0;
          }
        }
      )
    );

  }

  generation = 0;
  drawGrid();
}


document.getElementById("randomBtn").onclick = randomize;

document.getElementById("clearBtn").onclick = () => {

  stopSimulation();

  if (currentAlgorithm === "dla") {
    initializeDLA();
  } else if (currentAlgorithm === "noise") {
    initializeNoise();
  } else if (currentAlgorithm === "maze") {
    initializeMaze();
  } else if (currentAlgorithm === "reaction") {

    chemicalA = new Float32Array(cols * rows);
    chemicalB = new Float32Array(cols * rows);

    chemicalA.fill(1.0);

  } else {

    grid = createGrid();

  }

  generation = 0;
  drawGrid();
};



let isDrawing = false;

function paintOnCanvas(event) {

  const rect = canvas.getBoundingClientRect();

  const x = Math.floor(
    (event.clientX - rect.left) *
    canvas.width / rect.width / cellSize
  );

  const y = Math.floor(
    (event.clientY - rect.top) *
    canvas.height / rect.height / cellSize
  );

  if (x < 0 || x >= cols || y < 0 || y >= rows) {
    return;
  }

  if (currentAlgorithm === "reaction") {

    // Inject chemical B
    injectChemicalB(x, y);

  } else if (currentAlgorithm === "life") {

    // Draw living cells
    grid[y][x] = 1;
    drawGrid();

  } else if (currentAlgorithm === "cyclic") {

    // Change the cell's color state
    grid[y][x] = (grid[y][x] + 1) % numStates;
    drawGrid();

  }
}

canvas.addEventListener("pointerdown", event => {
  if (event.button !== 0) return;

  isDrawing = true;
  canvas.setPointerCapture(event.pointerId);

  paintOnCanvas(event);
});

canvas.addEventListener("pointermove", event => {
  if (isDrawing) {
    paintOnCanvas(event);
  }
});

canvas.addEventListener("pointerup", () => {
  isDrawing = false;
});

canvas.addEventListener("pointercancel", () => {
  isDrawing = false;
});

canvas.addEventListener("lostpointercapture", () => {
  isDrawing = false;
});

// Track mouse position for Boids
canvas.addEventListener("pointermove", event => {

  const rect = canvas.getBoundingClientRect();

  boidsMouseX =
    (event.clientX - rect.left) *
    canvas.width / rect.width;

  boidsMouseY =
    (event.clientY - rect.top) *
    canvas.height / rect.height;

  boidsMouseActive = true;
});

canvas.addEventListener("pointerenter", event => {
  boidsMouseActive = true;
});

canvas.addEventListener("pointerleave", () => {
  boidsMouseActive = false;
});

drawGrid();


function countNeighbors(x, y) {
  let count = 0;

  for (let dy = -1; dy <= 1; dy++) {
    for (let dx = -1; dx <= 1; dx++) {

      if (dx === 0 && dy === 0) continue;

      const nx = (x + dx + cols) % cols;
      const ny = (y + dy + rows) % rows;

      count += grid[ny][nx];
    }
  }

  return count;
}

function nextLifeGeneration() {
  const newGrid = createGrid();

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const neighbors = countNeighbors(x, y);
      const alive = grid[y][x] === 1;

      if (alive && (neighbors === 2 || neighbors === 3)) {
        newGrid[y][x] = 1;
      } else if (!alive && neighbors === 3) {
        newGrid[y][x] = 1;
      }

    }
  }

  grid = newGrid;
  generation++;
  drawGrid();
}

function nextCyclicGeneration() {
  const newGrid = createGrid();

  for (let y = 0; y < rows; y++) {
    for (let x = 0; x < cols; x++) {

      const current = grid[y][x];
      const next = (current + 1) % numStates;

      let advance = false;

      for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++) {

          if (dx === 0 && dy === 0) continue;

          const nx = (x + dx + cols) % cols;
          const ny = (y + dy + rows) % rows;

          if (grid[ny][nx] === next) {
            advance = true;
          }
        }
      }

      newGrid[y][x] = advance ? next : current;
    }
  }

  grid = newGrid;
  generation++;
  drawGrid();
}


function nextGeneration() {

  if (currentAlgorithm === "life") {

    nextLifeGeneration();

  } else if (currentAlgorithm === "cyclic") {

    nextCyclicGeneration();

  } else if (currentAlgorithm === "reaction") {

    // Run 10 reaction-diffusion steps
    for (let i = 0; i < 10; i++) {
      nextReactionGeneration();
    }

    drawGrid();

  } else if (currentAlgorithm === "maze") {

    if (bfsActive) {

      nextBFSStep();

    } else if (dfsActive) {

      nextDFSStep();

    } else if (astarActive) {

      nextAStarStep();

    } else if (!mazeComplete) {

      for (let i = 0; i < 5 && !mazeComplete; i++) {
        nextMazeGeneration();
      }

    }


} else if (currentAlgorithm === "noise") {

  // Move through the noise field
  noiseOffsetX += 0.10;
  noiseOffsetY += 0.05;

  updateNoiseGrid();

  // Update particles only in Particle Flow mode
  if (noiseDisplayMode === "particles") {
    updateParticles();
  }

  generation++;
  drawGrid();

}

else if (currentAlgorithm === "dla") {

  // Multiple random-walk steps per animation update
  for (let i = 0; i < 500 && !dlaComplete; i++) {
    nextDLAStep();
  }

  drawGrid();

}

else if (currentAlgorithm === "ant") {

  // Perform multiple ant steps per update
  for (let i = 0; i < 20; i++) {
    nextAntStep();
  }

  drawGrid();

}

else if (currentAlgorithm === "wfc") {

  // Collapse one cell per animation update
  nextWFCStep();

  drawGrid();

}

else if (currentAlgorithm === "boids") {

  updateBoids();
  drawGrid();

}


}


document.getElementById("stepBtn").onclick = () => {
  if (!running) {
    nextGeneration();
  }
};

let simulationInterval = null;


function stopSimulation() {
  running = false;

  clearInterval(simulationInterval);
  simulationInterval = null;

  document.getElementById("startBtn").textContent = "Start";
}

function startSimulation() {
  clearInterval(simulationInterval);

  running = true;

  document.getElementById("startBtn").textContent = "Pause";

  simulationInterval = setInterval(() => {
    nextGeneration();
  }, 1000 / simulationSpeed);
}

document.getElementById("startBtn").onclick = () => {
  if (running) {
    stopSimulation();
  } else {
    startSimulation();
  }
};


const patterns = {
  glider: [
    [1, 0],
    [2, 1],
    [0, 2],
    [1, 2],
    [2, 2]
  ],

  blinker: [
    [0, 0],
    [1, 0],
    [2, 0]
  ],

  toad: [
    [1, 0],
    [2, 0],
    [3, 0],
    [0, 1],
    [1, 1],
    [2, 1]
  ]
};

document.getElementById("loadPatternBtn").onclick = () => {

  running = false;
  clearInterval(simulationInterval);
  simulationInterval = null;

  document.getElementById("startBtn").textContent = "Start";

  grid = createGrid();
  generation = 0;

  const selected =
    document.getElementById("patternSelect").value;

  const pattern = patterns[selected];

  const offsetX = Math.floor(cols / 2);
  const offsetY = Math.floor(rows / 2);

  for (const [dx, dy] of pattern) {
    const x = (offsetX + dx) % cols;
    const y = (offsetY + dy) % rows;

    grid[y][x] = 1;
  }

  drawGrid();
};

const speedSlider = document.getElementById("speedSlider");
const speedValue = document.getElementById("speedValue");

speedSlider.addEventListener("input", () => {
  simulationSpeed = Number(speedSlider.value);

  speedValue.textContent =
    simulationSpeed + " generations/sec";

  if (running) {
    startSimulation();
  }
});

document.getElementById("gridSizeSelect").addEventListener(
  "change",
  event => {

    stopSimulation();

    resizeCanvasGeometry();
    randomize();
  }
);


document.getElementById("algorithmSelect").addEventListener(
  "change",
  event => {

    stopSimulation();

    currentAlgorithm = event.target.value;
    updateAlgorithmSubtitle();
    generation = 0;
    
    if (currentAlgorithm === "boids") {

    initializeBoids();

    } else if (currentAlgorithm === "wfc") {

    initializeWFC();


    } else if (currentAlgorithm === "ant") {

    initializeAnt();


    } else if (currentAlgorithm === "dla") {

    initializeDLA();


    } else if (currentAlgorithm === "noise") {

    initializeNoise();


    } else if (currentAlgorithm === "maze") {

    initializeMaze();

    } else if (currentAlgorithm === "reaction") {

    initializeReaction();


    } else if (currentAlgorithm === "cyclic") {

      // Generate random color states
      grid = Array.from(
        { length: rows },
        () => Array.from(
          { length: cols },
          () => Math.floor(Math.random() * numStates)
        )
      );

    } else {

      // Initialize Game of Life
      grid = createGrid();

    }

    // Show preset patterns only for Game of Life
    document.querySelector(".pattern-controls").style.display =
      currentAlgorithm === "life" ? "flex" : "none";

    // Show color-state slider only for cyclic automata
    stateSetting.style.display =
      currentAlgorithm === "cyclic" ? "flex" : "none";
    feedSetting.style.display =
    currentAlgorithm === "reaction" ? "flex" : "none";

    killSetting.style.display =
    currentAlgorithm === "reaction" ? "flex" : "none";

    paletteSetting.style.display =
    currentAlgorithm === "reaction" ? "flex" : "none";

    solveMazeBtn.style.display =
    currentAlgorithm === "maze" ? "inline-block" : "none";

    pathfindingControls.style.display =
    currentAlgorithm === "maze" ? "flex" : "none";

    
document.getElementById("pathStats").style.display =
  currentAlgorithm === "maze" ? "block" : "none";

  mazeComplexitySetting.style.display =
  currentAlgorithm === "maze" ? "flex" : "none";

  noiseScaleSetting.style.display =
  currentAlgorithm === "noise" ? "flex" : "none";

  noiseDisplaySetting.style.display =
  currentAlgorithm === "noise" ? "flex" : "none";

  antRuleSetting.style.display =
  currentAlgorithm === "ant" ? "flex" : "none";

  wfcTileSetting.style.display =
  currentAlgorithm === "wfc" ? "flex" : "none";


boidsSeparationSetting.style.display =
  currentAlgorithm === "boids" ? "flex" : "none";

boidsAlignmentSetting.style.display =
  currentAlgorithm === "boids" ? "flex" : "none";

boidsCohesionSetting.style.display =
  currentAlgorithm === "boids" ? "flex" : "none";

boidsMouseSetting.style.display =
  currentAlgorithm === "boids" ? "flex" : "none";

    drawGrid();
  }
);


const stateSlider = document.getElementById("stateSlider");
const stateValue = document.getElementById("stateValue");
const stateSetting = document.getElementById("stateSetting");

stateSetting.style.display = "none";

stateSlider.addEventListener("input", () => {
  numStates = Number(stateSlider.value);

  stateValue.textContent = numStates + " states";

  if (currentAlgorithm === "cyclic") {
    randomize();
  }
});


const feedSetting = document.getElementById("feedSetting");
const killSetting = document.getElementById("killSetting");

const feedSlider = document.getElementById("feedSlider");
const killSlider = document.getElementById("killSlider");

const feedValue = document.getElementById("feedValue");
const killValue = document.getElementById("killValue");

// Hide these controls initially
feedSetting.style.display = "none";
killSetting.style.display = "none";

feedSlider.addEventListener("input", () => {
  feedRate = Number(feedSlider.value);
  feedValue.textContent = feedRate.toFixed(3);
});

killSlider.addEventListener("input", () => {
  killRate = Number(killSlider.value);
  killValue.textContent = killRate.toFixed(3);
});

const paletteSetting = document.getElementById("paletteSetting");
const paletteSelect = document.getElementById("paletteSelect");

// Hide the palette selector initially
paletteSetting.style.display = "none";

paletteSelect.addEventListener("change", () => {
  currentPalette = paletteSelect.value;

  // Recolor the existing simulation immediately
  drawGrid();
});

function updateAlgorithmSubtitle() {
  const subtitle = document.getElementById("algorithmSubtitle");

  const algorithmNames = {
    life: "Conway's Game of Life",
    cyclic: "Cyclic Cellular Automata",
    reaction: "Gray–Scott Reaction-Diffusion",
    maze: "Randomized Depth-First Search Maze Generation",
    noise: "2D Procedural Value Noise",
    dla: "Diffusion-Limited Aggregation",
    ant: "Langton's Ant",
    wfc: "Wave Function Collapse",
    boids: "Boids — Flocking Simulation"
  };

  subtitle.textContent = algorithmNames[currentAlgorithm];
}

const solveMazeBtn = document.getElementById("solveMazeBtn");


solveMazeBtn.addEventListener("click", () => {

  if (!mazeComplete) {
    alert("Generate the maze first!");
    return;
  }

  stopSimulation();
  resetPathStats();

  // Reset both pathfinding algorithms
  bfsQueue = [];
  bfsVisited = [];
  bfsParents = [];
  bfsPath = [];
  bfsActive = false;
  bfsComplete = false;

  dfsStack = [];
  dfsVisited = [];
  dfsParents = [];
  dfsPath = [];
  dfsActive = false;
  dfsComplete = false;

  
    astarOpen = [];
    astarVisited = [];
    astarClosed = [];
    astarParents = [];
    astarGScore = [];
    astarPath = [];

    astarActive = false;
    astarComplete = false;
    astarCurrent = null;


  const selected =
    document.getElementById("pathfindingSelect").value;

  
if (selected === "bfs") {

  initializeBFS();

} else if (selected === "dfs") {

  initializeDFS();

} else if (selected === "astar") {

  initializeAStar();

}

  startSimulation();
});

const pathfindingControls =
  document.getElementById("pathfindingControls");

pathfindingControls.style.display = "none";


const mazeComplexitySetting =
  document.getElementById("mazeComplexitySetting");

const mazeComplexitySlider =
  document.getElementById("mazeComplexitySlider");

const mazeComplexityValue =
  document.getElementById("mazeComplexityValue");

mazeComplexitySlider.addEventListener("input", () => {

  mazeComplexity = Number(mazeComplexitySlider.value);

  mazeComplexityValue.textContent =
    mazeComplexity + "%";

});

const noiseScaleSetting =
  document.getElementById("noiseScaleSetting");

const noiseScaleSlider =
  document.getElementById("noiseScaleSlider");

const noiseScaleValue =
  document.getElementById("noiseScaleValue");

noiseScaleSlider.addEventListener("input", () => {

  noiseScale = Number(noiseScaleSlider.value);

  noiseScaleValue.textContent =
    noiseScale.toFixed(3);

  if (currentAlgorithm === "noise") {
    updateNoiseGrid();
    drawGrid();
  }

});

const noiseDisplaySetting =
  document.getElementById("noiseDisplaySetting");

const noiseDisplaySelect =
  document.getElementById("noiseDisplaySelect");

noiseDisplaySelect.addEventListener("change", () => {

  noiseDisplayMode = noiseDisplaySelect.value;

  if (noiseDisplayMode === "particles") {
    initializeParticles();
  }

  drawGrid();

});

// Fullscreen layout: resizing changes the simulation's grid dimensions.
// Reset the active simulation so all of its arrays match the new geometry.
let lastViewportWidth = window.innerWidth;
let lastViewportHeight = window.innerHeight;
window.addEventListener("resize", () => {
  if (window.innerWidth === lastViewportWidth &&
      window.innerHeight === lastViewportHeight) return;
  lastViewportWidth = window.innerWidth;
  lastViewportHeight = window.innerHeight;
  stopSimulation();
  resizeCanvasGeometry();
  randomize();
});

const togglePanelBtn = document.getElementById("togglePanelBtn");
const controlPanel = document.getElementById("controlPanel");
togglePanelBtn.addEventListener("click", () => {
  const hidden = controlPanel.classList.toggle("is-hidden");
  document.body.classList.toggle("panel-hidden", hidden);
  togglePanelBtn.textContent = hidden ? "Show Controls" : "Hide Controls";
  togglePanelBtn.setAttribute("aria-expanded", String(!hidden));
});

const antRuleSetting =
  document.getElementById("antRuleSetting");

const antRuleSelect =
  document.getElementById("antRuleSelect");

antRuleSelect.addEventListener("change", () => {

  antRule = antRuleSelect.value;

  stopSimulation();
  initializeAnt();
  drawGrid();

});

const wfcTileSetting =
  document.getElementById("wfcTileSetting");

const wfcTileSelect =
  document.getElementById("wfcTileSelect");

wfcTileSelect.addEventListener("change", () => {

  wfcTileSet = wfcTileSelect.value;

  stopSimulation();
  initializeWFC();
  drawGrid();

});

// Boids slider elements
const boidsSeparationSetting =
  document.getElementById("boidsSeparationSetting");

const boidsAlignmentSetting =
  document.getElementById("boidsAlignmentSetting");

const boidsCohesionSetting =
  document.getElementById("boidsCohesionSetting");

const separationSlider =
  document.getElementById("separationSlider");

const alignmentSlider =
  document.getElementById("alignmentSlider");

const cohesionSlider =
  document.getElementById("cohesionSlider");

// Separation slider
separationSlider.addEventListener("input", () => {
  separationWeight = Number(separationSlider.value);

  document.getElementById("separationValue").textContent =
    separationWeight.toFixed(1);
});

// Alignment slider
alignmentSlider.addEventListener("input", () => {
  alignmentWeight = Number(alignmentSlider.value);

  document.getElementById("alignmentValue").textContent =
    alignmentWeight.toFixed(1);
});

// Cohesion slider
cohesionSlider.addEventListener("input", () => {
  cohesionWeight = Number(cohesionSlider.value);

  document.getElementById("cohesionValue").textContent =
    cohesionWeight.toFixed(1);
});

const boidsMouseSetting =
  document.getElementById("boidsMouseSetting");

const boidsMouseSelect =
  document.getElementById("boidsMouseSelect");

boidsMouseSelect.addEventListener("change", () => {
  boidsMouseMode = boidsMouseSelect.value;
});
