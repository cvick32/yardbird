import {
  createContext,
  Dispatch,
  PropsWithChildren,
  useContext,
  useReducer,
} from "react";
import { Artifact, readFile } from "./fetch";

const localStorageKey = "scarecrow-local-files";

export interface FileContext {
  files: Map<string, Artifact>;
}

const FileContext = createContext<FileContext>({ files: new Map() });
const FileDispatchContext = createContext<Dispatch<FileContext>>((_) => {});

export function FileProvider({ children }: PropsWithChildren<{}>) {
  const savedFiles = localStorage.getItem(localStorageKey);
  console.log("saved:", savedFiles);
  let initialFiles = { files: new Map() };
  if (!!savedFiles) {
    const raw = JSON.parse(savedFiles);
    console.log("raw", raw, typeof raw);
    initialFiles = {
      files: new Map(raw.files),
    };
    console.log("here", initialFiles);
  }

  const [files, dispatch] = useReducer(fileReducer, initialFiles);

  return (
    <FileContext.Provider value={files}>
      <FileDispatchContext.Provider value={dispatch}>
        {children}
      </FileDispatchContext.Provider>
    </FileContext.Provider>
  );
}

export function useFiles() {
  const context = useContext(FileContext);
  const dispatch = useContext(FileDispatchContext);
  if (!context || !dispatch) {
    throw new Error("useFiles must be used within an FileProvider");
  }

  const setFiles = (files: File[]) => {
    Promise.allSettled(files.map((f) => readFile(f))).then((art_prom) => {
      const artifacts = art_prom
        .filter((prom) => prom.status === "fulfilled")
        .map((prom) => prom.value);
      dispatch({
        files: new Map(artifacts.map((art) => [art.id, art])),
      });
    });
  };

  const deleteFile = (id: string) => {
    context.files.delete(id);
    dispatch({
      files: new Map(context.files),
    });
  };

  return { files: context.files, setFiles, deleteFile };
}

function fileReducer(_oldFiles: FileContext, newFiles: FileContext) {
  localStorage.setItem(
    localStorageKey,
    JSON.stringify({
      files: [...newFiles.files.entries()],
    }),
  );
  return newFiles;
}
