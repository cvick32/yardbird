import { createContext, useContext } from "react";
import type { TrainingDatabaseId, TrainingDatabaseOption } from "./types";

export interface TrainingDatabaseContextValue {
  selectedDatabase: TrainingDatabaseId;
  selectedOption: TrainingDatabaseOption;
  options: TrainingDatabaseOption[];
  setSelectedDatabase: (database: TrainingDatabaseId) => void;
}

export const DEFAULT_TRAINING_DATABASE_OPTIONS: TrainingDatabaseOption[] = [
  { id: "local", label: "Local yardbird", configured: true },
  { id: "lab", label: "Lab training", configured: true },
];

export const TrainingDatabaseContext =
  createContext<TrainingDatabaseContextValue | null>(null);

export function useTrainingDatabase(): TrainingDatabaseContextValue {
  const context = useContext(TrainingDatabaseContext);
  if (!context) {
    throw new Error("useTrainingDatabase must be used within a provider");
  }
  return context;
}
