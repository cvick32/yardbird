import { Artifact, Benchmark, getResult, getStatus } from "../fetch";

export const getScatterColor = (point: any) => {
    return point.abs_time > point.con_time ? "#f08080" : "#bcf5bc"; // Red if abstract > concrete, Green otherwise
};

export const getBackgroundColor = (abs_time: number, con_time: number) => {
    if (abs_time > con_time) {
      return "#f08080";
    } else {
      return "#bcf5bc";
    }
  };

  export function getSuccessfulBenchmarks(artifact: Artifact): Benchmark[] {
    if (artifact.benchmarks === undefined) {
      return [];
    } else {
      return artifact.benchmarks?.filter(
        (benchmark) => getStatus(getResult(benchmark)) === "success",
      );
    }
  }

export function getFoundProofBenchmarks(artifact: Artifact): Benchmark[] {
    if (artifact.benchmarks === undefined) {
      return [];
    } else {
      return artifact.benchmarks?.filter(
        (benchmark) => getStatus(getResult(benchmark)) === "found-proof",
      );
    }
  }
  
  export function generateLogTicks(min: number, max: number) {
    const ticks: number[] = [];
    let base = Math.pow(10, Math.floor(Math.log10(min)));
    while (base <= max) {
      [1, 2, 5].forEach((mult) => {
        const tick = base * mult;
        if (tick >= min && tick <= max) {
          ticks.push(tick);
        }
      });
      base *= 10;
    }
    return ticks;
  }