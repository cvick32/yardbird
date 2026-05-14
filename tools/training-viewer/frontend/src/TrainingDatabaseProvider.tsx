import { useCallback, useEffect, useMemo, useState, type ReactNode } from "react";
import { api } from "./api";
import {
  DEFAULT_TRAINING_DATABASE_OPTIONS,
  TrainingDatabaseContext,
} from "./trainingDatabase";
import type { TrainingDatabaseId, TrainingDatabaseOption } from "./types";

const STORAGE_KEY = "yardbird.trainingViewer.database";

function parseDatabase(value: string | null): TrainingDatabaseId {
  return value === "lab" ? "lab" : "local";
}

function readStoredDatabase(): TrainingDatabaseId {
  try {
    return parseDatabase(window.localStorage.getItem(STORAGE_KEY));
  } catch {
    return "local";
  }
}

function storeDatabase(database: TrainingDatabaseId): void {
  try {
    window.localStorage.setItem(STORAGE_KEY, database);
  } catch {
    // Non-persistent browser contexts can still use the in-memory state.
  }
}

export function TrainingDatabaseProvider({
  children,
}: {
  children: ReactNode;
}) {
  const [selectedDatabase, setSelectedDatabaseState] =
    useState<TrainingDatabaseId>(readStoredDatabase);
  const [options, setOptions] = useState<TrainingDatabaseOption[]>(
    DEFAULT_TRAINING_DATABASE_OPTIONS,
  );

  useEffect(() => {
    let cancelled = false;
    api
      .trainingDatabases()
      .then((available) => {
        if (cancelled || available.length === 0) return;
        setOptions(available);
        setSelectedDatabaseState((current) => {
          const selected = available.find((option) => option.id === current);
          if (selected?.configured) return current;

          const fallback = available.find((option) => option.configured);
          if (!fallback) return current;
          storeDatabase(fallback.id);
          return fallback.id;
        });
      })
      .catch((err) => {
        console.error("Unable to load training database options:", err);
      });
    return () => {
      cancelled = true;
    };
  }, []);

  const setSelectedDatabase = useCallback((database: TrainingDatabaseId) => {
    setSelectedDatabaseState(database);
    storeDatabase(database);
  }, []);

  const value = useMemo(() => {
    const selectedOption =
      options.find((option) => option.id === selectedDatabase) ??
      DEFAULT_TRAINING_DATABASE_OPTIONS[0];
    return {
      selectedDatabase,
      selectedOption,
      options,
      setSelectedDatabase,
    };
  }, [options, selectedDatabase, setSelectedDatabase]);

  return (
    <TrainingDatabaseContext.Provider value={value}>
      {children}
    </TrainingDatabaseContext.Provider>
  );
}
