import { BrowserRouter, Routes, Route, useParams } from "react-router-dom";
import BenchmarkList from "./components/BenchmarkList";
import RunList from "./components/RunList";
import RunDetail from "./components/RunDetail";
import "./App.css";

function Layout() {
  const { runId } = useParams();
  return (
    <div className="layout">
      <BenchmarkList />
      {runId ? <RunDetail /> : <RunList />}
    </div>
  );
}

export default function App() {
  return (
    <BrowserRouter>
      <Routes>
        <Route path="/" element={<Layout />} />
        <Route path="/benchmarks/:benchmarkName" element={<Layout />} />
        <Route
          path="/benchmarks/:benchmarkName/runs/:runId"
          element={<Layout />}
        />
      </Routes>
    </BrowserRouter>
  );
}
